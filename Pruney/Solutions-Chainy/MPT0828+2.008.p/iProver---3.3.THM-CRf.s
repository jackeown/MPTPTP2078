%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:55:15 EST 2020

% Result     : Theorem 0.91s
% Output     : CNFRefutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 237 expanded)
%              Number of clauses        :   49 (  85 expanded)
%              Number of leaves         :    9 (  44 expanded)
%              Depth                    :   16
%              Number of atoms          :  203 ( 728 expanded)
%              Number of equality atoms :   84 ( 225 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( r1_tarski(k6_relat_1(X1),X2)
       => ( r1_tarski(X1,k2_relset_1(X1,X0,X2))
          & k1_relset_1(X1,X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( r1_tarski(k6_relat_1(X1),X2)
         => ( r1_tarski(X1,k2_relset_1(X1,X0,X2))
            & k1_relset_1(X1,X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(X1,k2_relset_1(X1,X0,X2))
        | k1_relset_1(X1,X0,X2) != X1 )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(X1,k2_relset_1(X1,X0,X2))
        | k1_relset_1(X1,X0,X2) != X1 )
      & r1_tarski(k6_relat_1(X1),X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f19])).

fof(f21,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_tarski(X1,k2_relset_1(X1,X0,X2))
          | k1_relset_1(X1,X0,X2) != X1 )
        & r1_tarski(k6_relat_1(X1),X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ( ~ r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2))
        | k1_relset_1(sK1,sK0,sK2) != sK1 )
      & r1_tarski(k6_relat_1(sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ( ~ r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2))
      | k1_relset_1(sK1,sK0,sK2) != sK1 )
    & r1_tarski(k6_relat_1(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f21])).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f32,plain,
    ( ~ r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2))
    | k1_relset_1(sK1,sK0,sK2) != sK1 ),
    inference(cnf_transformation,[],[f22])).

fof(f31,plain,(
    r1_tarski(k6_relat_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(k6_relat_1(X2),X3)
       => ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
          & r1_tarski(X2,k1_relset_1(X0,X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
        & r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
        & r1_tarski(X2,k1_relset_1(X0,X1,X3)) )
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f17])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X2,k2_relset_1(X0,X1,X3))
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X2,k1_relset_1(X0,X1,X3))
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_9,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_205,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_9])).

cnf(c_206,plain,
    ( v1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_205])).

cnf(c_232,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | k1_relat_1(k7_relat_1(X1,X0)) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_206])).

cnf(c_233,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK2))
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | k1_relat_1(k7_relat_1(sK2,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_232])).

cnf(c_293,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_233])).

cnf(c_440,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_293])).

cnf(c_295,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_233])).

cnf(c_317,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_295])).

cnf(c_321,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_293])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_196,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_9])).

cnf(c_197,plain,
    ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_196])).

cnf(c_534,plain,
    ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    inference(equality_resolution,[status(thm)],[c_197])).

cnf(c_7,negated_conjecture,
    ( ~ r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2))
    | k1_relset_1(sK1,sK0,sK2) != sK1 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_444,plain,
    ( k1_relset_1(sK1,sK0,sK2) != sK1
    | r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_8,negated_conjecture,
    ( r1_tarski(k6_relat_1(sK1),sK2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_297,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_500,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_297])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(X3,k2_relset_1(X1,X2,X0))
    | ~ r1_tarski(k6_relat_1(X3),X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_181,plain,
    ( r1_tarski(X0,k2_relset_1(X1,X2,X3))
    | ~ r1_tarski(k6_relat_1(X0),X3)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_9])).

cnf(c_182,plain,
    ( r1_tarski(X0,k2_relset_1(X1,X2,sK2))
    | ~ r1_tarski(k6_relat_1(X0),sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_181])).

cnf(c_501,plain,
    ( r1_tarski(X0,k2_relset_1(sK1,sK0,sK2))
    | ~ r1_tarski(k6_relat_1(X0),sK2)
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_182])).

cnf(c_508,plain,
    ( ~ r1_tarski(k6_relat_1(sK1),sK2)
    | r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2))
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_501])).

cnf(c_529,plain,
    ( k1_relset_1(sK1,sK0,sK2) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_444,c_8,c_7,c_500,c_508])).

cnf(c_580,plain,
    ( k1_relat_1(sK2) != sK1 ),
    inference(demodulation,[status(thm)],[c_534,c_529])).

cnf(c_443,plain,
    ( r1_tarski(k6_relat_1(sK1),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(X3,k1_relset_1(X1,X2,X0))
    | ~ r1_tarski(k6_relat_1(X3),X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_166,plain,
    ( r1_tarski(X0,k1_relset_1(X1,X2,X3))
    | ~ r1_tarski(k6_relat_1(X0),X3)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_9])).

cnf(c_167,plain,
    ( r1_tarski(X0,k1_relset_1(X1,X2,sK2))
    | ~ r1_tarski(k6_relat_1(X0),sK2)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_166])).

cnf(c_442,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | r1_tarski(X2,k1_relset_1(X0,X1,sK2)) = iProver_top
    | r1_tarski(k6_relat_1(X2),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_167])).

cnf(c_694,plain,
    ( r1_tarski(X0,k1_relset_1(sK1,sK0,sK2)) = iProver_top
    | r1_tarski(k6_relat_1(X0),sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_442])).

cnf(c_695,plain,
    ( r1_tarski(X0,k1_relat_1(sK2)) = iProver_top
    | r1_tarski(k6_relat_1(X0),sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_694,c_534])).

cnf(c_758,plain,
    ( r1_tarski(sK1,k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_443,c_695])).

cnf(c_294,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK2))
    | k1_relat_1(k7_relat_1(sK2,X0)) = X0
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_233])).

cnf(c_439,plain,
    ( k1_relat_1(k7_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_294])).

cnf(c_795,plain,
    ( k1_relat_1(k7_relat_1(sK2,sK1)) = sK1
    | sP1_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_758,c_439])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_0,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_119,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_3,c_0])).

cnf(c_123,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_119,c_3,c_2,c_0])).

cnf(c_157,plain,
    ( k7_relat_1(X0,X1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_123,c_9])).

cnf(c_158,plain,
    ( k7_relat_1(sK2,X0) = sK2
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(unflattening,[status(thm)],[c_157])).

cnf(c_516,plain,
    ( k7_relat_1(sK2,sK1) = sK2 ),
    inference(equality_resolution,[status(thm)],[c_158])).

cnf(c_796,plain,
    ( k1_relat_1(sK2) = sK1
    | sP1_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_795,c_516])).

cnf(c_850,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_440,c_317,c_321,c_580,c_796])).

cnf(c_854,plain,
    ( $false ),
    inference(equality_resolution,[status(thm)],[c_850])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.07  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.08  % Command    : iproveropt_run.sh %d %s
% 0.07/0.27  % Computer   : n009.cluster.edu
% 0.07/0.27  % Model      : x86_64 x86_64
% 0.07/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.27  % Memory     : 8042.1875MB
% 0.07/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.27  % CPULimit   : 60
% 0.07/0.27  % WCLimit    : 600
% 0.07/0.27  % DateTime   : Tue Dec  1 12:52:41 EST 2020
% 0.07/0.27  % CPUTime    : 
% 0.07/0.27  % Running in FOF mode
% 0.91/0.85  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.91/0.85  
% 0.91/0.85  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.91/0.85  
% 0.91/0.85  ------  iProver source info
% 0.91/0.85  
% 0.91/0.85  git: date: 2020-06-30 10:37:57 +0100
% 0.91/0.85  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.91/0.85  git: non_committed_changes: false
% 0.91/0.85  git: last_make_outside_of_git: false
% 0.91/0.85  
% 0.91/0.85  ------ 
% 0.91/0.85  
% 0.91/0.85  ------ Input Options
% 0.91/0.85  
% 0.91/0.85  --out_options                           all
% 0.91/0.85  --tptp_safe_out                         true
% 0.91/0.85  --problem_path                          ""
% 0.91/0.85  --include_path                          ""
% 0.91/0.85  --clausifier                            res/vclausify_rel
% 0.91/0.85  --clausifier_options                    --mode clausify
% 0.91/0.85  --stdin                                 false
% 0.91/0.85  --stats_out                             all
% 0.91/0.85  
% 0.91/0.85  ------ General Options
% 0.91/0.85  
% 0.91/0.85  --fof                                   false
% 0.91/0.85  --time_out_real                         305.
% 0.91/0.85  --time_out_virtual                      -1.
% 0.91/0.85  --symbol_type_check                     false
% 0.91/0.85  --clausify_out                          false
% 0.91/0.85  --sig_cnt_out                           false
% 0.91/0.85  --trig_cnt_out                          false
% 0.91/0.85  --trig_cnt_out_tolerance                1.
% 0.91/0.85  --trig_cnt_out_sk_spl                   false
% 0.91/0.85  --abstr_cl_out                          false
% 0.91/0.85  
% 0.91/0.85  ------ Global Options
% 0.91/0.85  
% 0.91/0.85  --schedule                              default
% 0.91/0.85  --add_important_lit                     false
% 0.91/0.85  --prop_solver_per_cl                    1000
% 0.91/0.85  --min_unsat_core                        false
% 0.91/0.85  --soft_assumptions                      false
% 0.91/0.85  --soft_lemma_size                       3
% 0.91/0.85  --prop_impl_unit_size                   0
% 0.91/0.85  --prop_impl_unit                        []
% 0.91/0.85  --share_sel_clauses                     true
% 0.91/0.85  --reset_solvers                         false
% 0.91/0.85  --bc_imp_inh                            [conj_cone]
% 0.91/0.85  --conj_cone_tolerance                   3.
% 0.91/0.85  --extra_neg_conj                        none
% 0.91/0.85  --large_theory_mode                     true
% 0.91/0.85  --prolific_symb_bound                   200
% 0.91/0.85  --lt_threshold                          2000
% 0.91/0.85  --clause_weak_htbl                      true
% 0.91/0.85  --gc_record_bc_elim                     false
% 0.91/0.85  
% 0.91/0.85  ------ Preprocessing Options
% 0.91/0.85  
% 0.91/0.85  --preprocessing_flag                    true
% 0.91/0.85  --time_out_prep_mult                    0.1
% 0.91/0.85  --splitting_mode                        input
% 0.91/0.85  --splitting_grd                         true
% 0.91/0.85  --splitting_cvd                         false
% 0.91/0.85  --splitting_cvd_svl                     false
% 0.91/0.85  --splitting_nvd                         32
% 0.91/0.85  --sub_typing                            true
% 0.91/0.85  --prep_gs_sim                           true
% 0.91/0.85  --prep_unflatten                        true
% 0.91/0.85  --prep_res_sim                          true
% 0.91/0.85  --prep_upred                            true
% 0.91/0.85  --prep_sem_filter                       exhaustive
% 0.91/0.85  --prep_sem_filter_out                   false
% 0.91/0.85  --pred_elim                             true
% 0.91/0.85  --res_sim_input                         true
% 0.91/0.85  --eq_ax_congr_red                       true
% 0.91/0.85  --pure_diseq_elim                       true
% 0.91/0.85  --brand_transform                       false
% 0.91/0.85  --non_eq_to_eq                          false
% 0.91/0.85  --prep_def_merge                        true
% 0.91/0.85  --prep_def_merge_prop_impl              false
% 0.91/0.85  --prep_def_merge_mbd                    true
% 0.91/0.85  --prep_def_merge_tr_red                 false
% 0.91/0.85  --prep_def_merge_tr_cl                  false
% 0.91/0.85  --smt_preprocessing                     true
% 0.91/0.85  --smt_ac_axioms                         fast
% 0.91/0.85  --preprocessed_out                      false
% 0.91/0.85  --preprocessed_stats                    false
% 0.91/0.85  
% 0.91/0.85  ------ Abstraction refinement Options
% 0.91/0.85  
% 0.91/0.85  --abstr_ref                             []
% 0.91/0.85  --abstr_ref_prep                        false
% 0.91/0.85  --abstr_ref_until_sat                   false
% 0.91/0.85  --abstr_ref_sig_restrict                funpre
% 0.91/0.85  --abstr_ref_af_restrict_to_split_sk     false
% 0.91/0.85  --abstr_ref_under                       []
% 0.91/0.85  
% 0.91/0.85  ------ SAT Options
% 0.91/0.85  
% 0.91/0.85  --sat_mode                              false
% 0.91/0.85  --sat_fm_restart_options                ""
% 0.91/0.85  --sat_gr_def                            false
% 0.91/0.85  --sat_epr_types                         true
% 0.91/0.85  --sat_non_cyclic_types                  false
% 0.91/0.85  --sat_finite_models                     false
% 0.91/0.85  --sat_fm_lemmas                         false
% 0.91/0.85  --sat_fm_prep                           false
% 0.91/0.85  --sat_fm_uc_incr                        true
% 0.91/0.85  --sat_out_model                         small
% 0.91/0.85  --sat_out_clauses                       false
% 0.91/0.85  
% 0.91/0.85  ------ QBF Options
% 0.91/0.85  
% 0.91/0.85  --qbf_mode                              false
% 0.91/0.85  --qbf_elim_univ                         false
% 0.91/0.85  --qbf_dom_inst                          none
% 0.91/0.85  --qbf_dom_pre_inst                      false
% 0.91/0.85  --qbf_sk_in                             false
% 0.91/0.85  --qbf_pred_elim                         true
% 0.91/0.85  --qbf_split                             512
% 0.91/0.85  
% 0.91/0.85  ------ BMC1 Options
% 0.91/0.85  
% 0.91/0.85  --bmc1_incremental                      false
% 0.91/0.85  --bmc1_axioms                           reachable_all
% 0.91/0.85  --bmc1_min_bound                        0
% 0.91/0.85  --bmc1_max_bound                        -1
% 0.91/0.85  --bmc1_max_bound_default                -1
% 0.91/0.85  --bmc1_symbol_reachability              true
% 0.91/0.85  --bmc1_property_lemmas                  false
% 0.91/0.85  --bmc1_k_induction                      false
% 0.91/0.85  --bmc1_non_equiv_states                 false
% 0.91/0.85  --bmc1_deadlock                         false
% 0.91/0.85  --bmc1_ucm                              false
% 0.91/0.85  --bmc1_add_unsat_core                   none
% 0.91/0.85  --bmc1_unsat_core_children              false
% 0.91/0.85  --bmc1_unsat_core_extrapolate_axioms    false
% 0.91/0.85  --bmc1_out_stat                         full
% 0.91/0.85  --bmc1_ground_init                      false
% 0.91/0.85  --bmc1_pre_inst_next_state              false
% 0.91/0.85  --bmc1_pre_inst_state                   false
% 0.91/0.85  --bmc1_pre_inst_reach_state             false
% 0.91/0.85  --bmc1_out_unsat_core                   false
% 0.91/0.85  --bmc1_aig_witness_out                  false
% 0.91/0.85  --bmc1_verbose                          false
% 0.91/0.85  --bmc1_dump_clauses_tptp                false
% 0.91/0.85  --bmc1_dump_unsat_core_tptp             false
% 0.91/0.85  --bmc1_dump_file                        -
% 0.91/0.85  --bmc1_ucm_expand_uc_limit              128
% 0.91/0.85  --bmc1_ucm_n_expand_iterations          6
% 0.91/0.85  --bmc1_ucm_extend_mode                  1
% 0.91/0.85  --bmc1_ucm_init_mode                    2
% 0.91/0.85  --bmc1_ucm_cone_mode                    none
% 0.91/0.85  --bmc1_ucm_reduced_relation_type        0
% 0.91/0.85  --bmc1_ucm_relax_model                  4
% 0.91/0.85  --bmc1_ucm_full_tr_after_sat            true
% 0.91/0.85  --bmc1_ucm_expand_neg_assumptions       false
% 0.91/0.85  --bmc1_ucm_layered_model                none
% 0.91/0.85  --bmc1_ucm_max_lemma_size               10
% 0.91/0.85  
% 0.91/0.85  ------ AIG Options
% 0.91/0.85  
% 0.91/0.85  --aig_mode                              false
% 0.91/0.85  
% 0.91/0.85  ------ Instantiation Options
% 0.91/0.85  
% 0.91/0.85  --instantiation_flag                    true
% 0.91/0.85  --inst_sos_flag                         false
% 0.91/0.85  --inst_sos_phase                        true
% 0.91/0.85  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.91/0.85  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.91/0.85  --inst_lit_sel_side                     num_symb
% 0.91/0.85  --inst_solver_per_active                1400
% 0.91/0.85  --inst_solver_calls_frac                1.
% 0.91/0.85  --inst_passive_queue_type               priority_queues
% 0.91/0.85  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.91/0.85  --inst_passive_queues_freq              [25;2]
% 0.91/0.85  --inst_dismatching                      true
% 0.91/0.85  --inst_eager_unprocessed_to_passive     true
% 0.91/0.85  --inst_prop_sim_given                   true
% 0.91/0.85  --inst_prop_sim_new                     false
% 0.91/0.85  --inst_subs_new                         false
% 0.91/0.85  --inst_eq_res_simp                      false
% 0.91/0.85  --inst_subs_given                       false
% 0.91/0.85  --inst_orphan_elimination               true
% 0.91/0.85  --inst_learning_loop_flag               true
% 0.91/0.85  --inst_learning_start                   3000
% 0.91/0.85  --inst_learning_factor                  2
% 0.91/0.85  --inst_start_prop_sim_after_learn       3
% 0.91/0.85  --inst_sel_renew                        solver
% 0.91/0.85  --inst_lit_activity_flag                true
% 0.91/0.85  --inst_restr_to_given                   false
% 0.91/0.85  --inst_activity_threshold               500
% 0.91/0.85  --inst_out_proof                        true
% 0.91/0.85  
% 0.91/0.85  ------ Resolution Options
% 0.91/0.85  
% 0.91/0.85  --resolution_flag                       true
% 0.91/0.85  --res_lit_sel                           adaptive
% 0.91/0.85  --res_lit_sel_side                      none
% 0.91/0.85  --res_ordering                          kbo
% 0.91/0.85  --res_to_prop_solver                    active
% 0.91/0.85  --res_prop_simpl_new                    false
% 0.91/0.85  --res_prop_simpl_given                  true
% 0.91/0.85  --res_passive_queue_type                priority_queues
% 0.91/0.85  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.91/0.85  --res_passive_queues_freq               [15;5]
% 0.91/0.85  --res_forward_subs                      full
% 0.91/0.85  --res_backward_subs                     full
% 0.91/0.85  --res_forward_subs_resolution           true
% 0.91/0.85  --res_backward_subs_resolution          true
% 0.91/0.85  --res_orphan_elimination                true
% 0.91/0.85  --res_time_limit                        2.
% 0.91/0.85  --res_out_proof                         true
% 0.91/0.85  
% 0.91/0.85  ------ Superposition Options
% 0.91/0.85  
% 0.91/0.85  --superposition_flag                    true
% 0.91/0.85  --sup_passive_queue_type                priority_queues
% 0.91/0.85  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.91/0.85  --sup_passive_queues_freq               [8;1;4]
% 0.91/0.85  --demod_completeness_check              fast
% 0.91/0.85  --demod_use_ground                      true
% 0.91/0.85  --sup_to_prop_solver                    passive
% 0.91/0.85  --sup_prop_simpl_new                    true
% 0.91/0.85  --sup_prop_simpl_given                  true
% 0.91/0.85  --sup_fun_splitting                     false
% 0.91/0.85  --sup_smt_interval                      50000
% 0.91/0.85  
% 0.91/0.85  ------ Superposition Simplification Setup
% 0.91/0.85  
% 0.91/0.85  --sup_indices_passive                   []
% 0.91/0.85  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.91/0.85  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.91/0.85  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.91/0.85  --sup_full_triv                         [TrivRules;PropSubs]
% 0.91/0.85  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.91/0.85  --sup_full_bw                           [BwDemod]
% 0.91/0.85  --sup_immed_triv                        [TrivRules]
% 0.91/0.85  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.91/0.85  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.91/0.85  --sup_immed_bw_main                     []
% 0.91/0.85  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.91/0.85  --sup_input_triv                        [Unflattening;TrivRules]
% 0.91/0.85  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.91/0.85  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.91/0.85  
% 0.91/0.85  ------ Combination Options
% 0.91/0.85  
% 0.91/0.85  --comb_res_mult                         3
% 0.91/0.85  --comb_sup_mult                         2
% 0.91/0.85  --comb_inst_mult                        10
% 0.91/0.85  
% 0.91/0.85  ------ Debug Options
% 0.91/0.85  
% 0.91/0.85  --dbg_backtrace                         false
% 0.91/0.85  --dbg_dump_prop_clauses                 false
% 0.91/0.85  --dbg_dump_prop_clauses_file            -
% 0.91/0.85  --dbg_out_stat                          false
% 0.91/0.85  ------ Parsing...
% 0.91/0.85  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.91/0.85  
% 0.91/0.85  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 0.91/0.85  
% 0.91/0.85  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.91/0.85  
% 0.91/0.85  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.91/0.85  ------ Proving...
% 0.91/0.85  ------ Problem Properties 
% 0.91/0.85  
% 0.91/0.85  
% 0.91/0.85  clauses                                 9
% 0.91/0.85  conjectures                             2
% 0.91/0.85  EPR                                     1
% 0.91/0.85  Horn                                    8
% 0.91/0.85  unary                                   1
% 0.91/0.85  binary                                  5
% 0.91/0.85  lits                                    20
% 0.91/0.85  lits eq                                 9
% 0.91/0.85  fd_pure                                 0
% 0.91/0.85  fd_pseudo                               0
% 0.91/0.85  fd_cond                                 0
% 0.91/0.85  fd_pseudo_cond                          0
% 0.91/0.85  AC symbols                              0
% 0.91/0.85  
% 0.91/0.85  ------ Schedule dynamic 5 is on 
% 0.91/0.85  
% 0.91/0.85  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.91/0.85  
% 0.91/0.85  
% 0.91/0.85  ------ 
% 0.91/0.85  Current options:
% 0.91/0.85  ------ 
% 0.91/0.85  
% 0.91/0.85  ------ Input Options
% 0.91/0.85  
% 0.91/0.85  --out_options                           all
% 0.91/0.85  --tptp_safe_out                         true
% 0.91/0.85  --problem_path                          ""
% 0.91/0.85  --include_path                          ""
% 0.91/0.85  --clausifier                            res/vclausify_rel
% 0.91/0.85  --clausifier_options                    --mode clausify
% 0.91/0.85  --stdin                                 false
% 0.91/0.85  --stats_out                             all
% 0.91/0.85  
% 0.91/0.85  ------ General Options
% 0.91/0.85  
% 0.91/0.85  --fof                                   false
% 0.91/0.85  --time_out_real                         305.
% 0.91/0.85  --time_out_virtual                      -1.
% 0.91/0.85  --symbol_type_check                     false
% 0.91/0.85  --clausify_out                          false
% 0.91/0.85  --sig_cnt_out                           false
% 0.91/0.85  --trig_cnt_out                          false
% 0.91/0.85  --trig_cnt_out_tolerance                1.
% 0.91/0.85  --trig_cnt_out_sk_spl                   false
% 0.91/0.85  --abstr_cl_out                          false
% 0.91/0.85  
% 0.91/0.85  ------ Global Options
% 0.91/0.85  
% 0.91/0.85  --schedule                              default
% 0.91/0.85  --add_important_lit                     false
% 0.91/0.85  --prop_solver_per_cl                    1000
% 0.91/0.85  --min_unsat_core                        false
% 0.91/0.85  --soft_assumptions                      false
% 0.91/0.85  --soft_lemma_size                       3
% 0.91/0.85  --prop_impl_unit_size                   0
% 0.91/0.85  --prop_impl_unit                        []
% 0.91/0.85  --share_sel_clauses                     true
% 0.91/0.85  --reset_solvers                         false
% 0.91/0.85  --bc_imp_inh                            [conj_cone]
% 0.91/0.85  --conj_cone_tolerance                   3.
% 0.91/0.85  --extra_neg_conj                        none
% 0.91/0.85  --large_theory_mode                     true
% 0.91/0.85  --prolific_symb_bound                   200
% 0.91/0.85  --lt_threshold                          2000
% 0.91/0.85  --clause_weak_htbl                      true
% 0.91/0.85  --gc_record_bc_elim                     false
% 0.91/0.85  
% 0.91/0.85  ------ Preprocessing Options
% 0.91/0.85  
% 0.91/0.85  --preprocessing_flag                    true
% 0.91/0.85  --time_out_prep_mult                    0.1
% 0.91/0.85  --splitting_mode                        input
% 0.91/0.85  --splitting_grd                         true
% 0.91/0.85  --splitting_cvd                         false
% 0.91/0.85  --splitting_cvd_svl                     false
% 0.91/0.85  --splitting_nvd                         32
% 0.91/0.85  --sub_typing                            true
% 0.91/0.85  --prep_gs_sim                           true
% 0.91/0.85  --prep_unflatten                        true
% 0.91/0.85  --prep_res_sim                          true
% 0.91/0.85  --prep_upred                            true
% 0.91/0.85  --prep_sem_filter                       exhaustive
% 0.91/0.85  --prep_sem_filter_out                   false
% 0.91/0.85  --pred_elim                             true
% 0.91/0.85  --res_sim_input                         true
% 0.91/0.85  --eq_ax_congr_red                       true
% 0.91/0.85  --pure_diseq_elim                       true
% 0.91/0.85  --brand_transform                       false
% 0.91/0.85  --non_eq_to_eq                          false
% 0.91/0.85  --prep_def_merge                        true
% 0.91/0.85  --prep_def_merge_prop_impl              false
% 0.91/0.85  --prep_def_merge_mbd                    true
% 0.91/0.85  --prep_def_merge_tr_red                 false
% 0.91/0.85  --prep_def_merge_tr_cl                  false
% 0.91/0.85  --smt_preprocessing                     true
% 0.91/0.85  --smt_ac_axioms                         fast
% 0.91/0.85  --preprocessed_out                      false
% 0.91/0.85  --preprocessed_stats                    false
% 0.91/0.85  
% 0.91/0.85  ------ Abstraction refinement Options
% 0.91/0.85  
% 0.91/0.85  --abstr_ref                             []
% 0.91/0.85  --abstr_ref_prep                        false
% 0.91/0.85  --abstr_ref_until_sat                   false
% 0.91/0.85  --abstr_ref_sig_restrict                funpre
% 0.91/0.85  --abstr_ref_af_restrict_to_split_sk     false
% 0.91/0.85  --abstr_ref_under                       []
% 0.91/0.85  
% 0.91/0.85  ------ SAT Options
% 0.91/0.85  
% 0.91/0.85  --sat_mode                              false
% 0.91/0.85  --sat_fm_restart_options                ""
% 0.91/0.85  --sat_gr_def                            false
% 0.91/0.85  --sat_epr_types                         true
% 0.91/0.85  --sat_non_cyclic_types                  false
% 0.91/0.85  --sat_finite_models                     false
% 0.91/0.85  --sat_fm_lemmas                         false
% 0.91/0.85  --sat_fm_prep                           false
% 0.91/0.85  --sat_fm_uc_incr                        true
% 0.91/0.85  --sat_out_model                         small
% 0.91/0.85  --sat_out_clauses                       false
% 0.91/0.85  
% 0.91/0.85  ------ QBF Options
% 0.91/0.85  
% 0.91/0.85  --qbf_mode                              false
% 0.91/0.85  --qbf_elim_univ                         false
% 0.91/0.85  --qbf_dom_inst                          none
% 0.91/0.85  --qbf_dom_pre_inst                      false
% 0.91/0.85  --qbf_sk_in                             false
% 0.91/0.85  --qbf_pred_elim                         true
% 0.91/0.85  --qbf_split                             512
% 0.91/0.85  
% 0.91/0.85  ------ BMC1 Options
% 0.91/0.85  
% 0.91/0.85  --bmc1_incremental                      false
% 0.91/0.85  --bmc1_axioms                           reachable_all
% 0.91/0.85  --bmc1_min_bound                        0
% 0.91/0.85  --bmc1_max_bound                        -1
% 0.91/0.85  --bmc1_max_bound_default                -1
% 0.91/0.85  --bmc1_symbol_reachability              true
% 0.91/0.85  --bmc1_property_lemmas                  false
% 0.91/0.85  --bmc1_k_induction                      false
% 0.91/0.85  --bmc1_non_equiv_states                 false
% 0.91/0.85  --bmc1_deadlock                         false
% 0.91/0.85  --bmc1_ucm                              false
% 0.91/0.85  --bmc1_add_unsat_core                   none
% 0.91/0.85  --bmc1_unsat_core_children              false
% 0.91/0.85  --bmc1_unsat_core_extrapolate_axioms    false
% 0.91/0.85  --bmc1_out_stat                         full
% 0.91/0.85  --bmc1_ground_init                      false
% 0.91/0.85  --bmc1_pre_inst_next_state              false
% 0.91/0.85  --bmc1_pre_inst_state                   false
% 0.91/0.85  --bmc1_pre_inst_reach_state             false
% 0.91/0.85  --bmc1_out_unsat_core                   false
% 0.91/0.85  --bmc1_aig_witness_out                  false
% 0.91/0.85  --bmc1_verbose                          false
% 0.91/0.85  --bmc1_dump_clauses_tptp                false
% 0.91/0.85  --bmc1_dump_unsat_core_tptp             false
% 0.91/0.85  --bmc1_dump_file                        -
% 0.91/0.85  --bmc1_ucm_expand_uc_limit              128
% 0.91/0.85  --bmc1_ucm_n_expand_iterations          6
% 0.91/0.85  --bmc1_ucm_extend_mode                  1
% 0.91/0.85  --bmc1_ucm_init_mode                    2
% 0.91/0.85  --bmc1_ucm_cone_mode                    none
% 0.91/0.85  --bmc1_ucm_reduced_relation_type        0
% 0.91/0.85  --bmc1_ucm_relax_model                  4
% 0.91/0.85  --bmc1_ucm_full_tr_after_sat            true
% 0.91/0.85  --bmc1_ucm_expand_neg_assumptions       false
% 0.91/0.85  --bmc1_ucm_layered_model                none
% 0.91/0.85  --bmc1_ucm_max_lemma_size               10
% 0.91/0.85  
% 0.91/0.85  ------ AIG Options
% 0.91/0.85  
% 0.91/0.85  --aig_mode                              false
% 0.91/0.85  
% 0.91/0.85  ------ Instantiation Options
% 0.91/0.85  
% 0.91/0.85  --instantiation_flag                    true
% 0.91/0.85  --inst_sos_flag                         false
% 0.91/0.85  --inst_sos_phase                        true
% 0.91/0.85  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.91/0.85  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.91/0.85  --inst_lit_sel_side                     none
% 0.91/0.85  --inst_solver_per_active                1400
% 0.91/0.85  --inst_solver_calls_frac                1.
% 0.91/0.85  --inst_passive_queue_type               priority_queues
% 0.91/0.85  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.91/0.85  --inst_passive_queues_freq              [25;2]
% 0.91/0.85  --inst_dismatching                      true
% 0.91/0.85  --inst_eager_unprocessed_to_passive     true
% 0.91/0.85  --inst_prop_sim_given                   true
% 0.91/0.85  --inst_prop_sim_new                     false
% 0.91/0.85  --inst_subs_new                         false
% 0.91/0.85  --inst_eq_res_simp                      false
% 0.91/0.85  --inst_subs_given                       false
% 0.91/0.85  --inst_orphan_elimination               true
% 0.91/0.85  --inst_learning_loop_flag               true
% 0.91/0.85  --inst_learning_start                   3000
% 0.91/0.85  --inst_learning_factor                  2
% 0.91/0.85  --inst_start_prop_sim_after_learn       3
% 0.91/0.85  --inst_sel_renew                        solver
% 0.91/0.85  --inst_lit_activity_flag                true
% 0.91/0.85  --inst_restr_to_given                   false
% 0.91/0.85  --inst_activity_threshold               500
% 0.91/0.85  --inst_out_proof                        true
% 0.91/0.85  
% 0.91/0.85  ------ Resolution Options
% 0.91/0.85  
% 0.91/0.85  --resolution_flag                       false
% 0.91/0.85  --res_lit_sel                           adaptive
% 0.91/0.85  --res_lit_sel_side                      none
% 0.91/0.85  --res_ordering                          kbo
% 0.91/0.85  --res_to_prop_solver                    active
% 0.91/0.85  --res_prop_simpl_new                    false
% 0.91/0.85  --res_prop_simpl_given                  true
% 0.91/0.85  --res_passive_queue_type                priority_queues
% 0.91/0.85  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.91/0.85  --res_passive_queues_freq               [15;5]
% 0.91/0.85  --res_forward_subs                      full
% 0.91/0.85  --res_backward_subs                     full
% 0.91/0.85  --res_forward_subs_resolution           true
% 0.91/0.85  --res_backward_subs_resolution          true
% 0.91/0.85  --res_orphan_elimination                true
% 0.91/0.85  --res_time_limit                        2.
% 0.91/0.85  --res_out_proof                         true
% 0.91/0.85  
% 0.91/0.85  ------ Superposition Options
% 0.91/0.85  
% 0.91/0.85  --superposition_flag                    true
% 0.91/0.85  --sup_passive_queue_type                priority_queues
% 0.91/0.85  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.91/0.85  --sup_passive_queues_freq               [8;1;4]
% 0.91/0.85  --demod_completeness_check              fast
% 0.91/0.85  --demod_use_ground                      true
% 0.91/0.85  --sup_to_prop_solver                    passive
% 0.91/0.85  --sup_prop_simpl_new                    true
% 0.91/0.85  --sup_prop_simpl_given                  true
% 0.91/0.85  --sup_fun_splitting                     false
% 0.91/0.85  --sup_smt_interval                      50000
% 0.91/0.85  
% 0.91/0.85  ------ Superposition Simplification Setup
% 0.91/0.85  
% 0.91/0.85  --sup_indices_passive                   []
% 0.91/0.85  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.91/0.85  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.91/0.85  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.91/0.85  --sup_full_triv                         [TrivRules;PropSubs]
% 0.91/0.85  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.91/0.85  --sup_full_bw                           [BwDemod]
% 0.91/0.85  --sup_immed_triv                        [TrivRules]
% 0.91/0.85  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.91/0.85  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.91/0.85  --sup_immed_bw_main                     []
% 0.91/0.85  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.91/0.85  --sup_input_triv                        [Unflattening;TrivRules]
% 0.91/0.85  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.91/0.85  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.91/0.85  
% 0.91/0.85  ------ Combination Options
% 0.91/0.85  
% 0.91/0.85  --comb_res_mult                         3
% 0.91/0.85  --comb_sup_mult                         2
% 0.91/0.85  --comb_inst_mult                        10
% 0.91/0.85  
% 0.91/0.85  ------ Debug Options
% 0.91/0.85  
% 0.91/0.85  --dbg_backtrace                         false
% 0.91/0.85  --dbg_dump_prop_clauses                 false
% 0.91/0.85  --dbg_dump_prop_clauses_file            -
% 0.91/0.85  --dbg_out_stat                          false
% 0.91/0.85  
% 0.91/0.85  
% 0.91/0.85  
% 0.91/0.85  
% 0.91/0.85  ------ Proving...
% 0.91/0.85  
% 0.91/0.85  
% 0.91/0.85  % SZS status Theorem for theBenchmark.p
% 0.91/0.85  
% 0.91/0.85   Resolution empty clause
% 0.91/0.85  
% 0.91/0.85  % SZS output start CNFRefutation for theBenchmark.p
% 0.91/0.85  
% 0.91/0.85  fof(f2,axiom,(
% 0.91/0.85    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 0.91/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.91/0.85  
% 0.91/0.85  fof(f12,plain,(
% 0.91/0.85    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.91/0.85    inference(ennf_transformation,[],[f2])).
% 0.91/0.85  
% 0.91/0.85  fof(f13,plain,(
% 0.91/0.85    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.91/0.85    inference(flattening,[],[f12])).
% 0.91/0.85  
% 0.91/0.85  fof(f24,plain,(
% 0.91/0.85    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.91/0.85    inference(cnf_transformation,[],[f13])).
% 0.91/0.85  
% 0.91/0.85  fof(f3,axiom,(
% 0.91/0.85    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.91/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.91/0.85  
% 0.91/0.85  fof(f14,plain,(
% 0.91/0.85    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.91/0.85    inference(ennf_transformation,[],[f3])).
% 0.91/0.85  
% 0.91/0.85  fof(f25,plain,(
% 0.91/0.85    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.91/0.85    inference(cnf_transformation,[],[f14])).
% 0.91/0.85  
% 0.91/0.85  fof(f7,conjecture,(
% 0.91/0.85    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(k6_relat_1(X1),X2) => (r1_tarski(X1,k2_relset_1(X1,X0,X2)) & k1_relset_1(X1,X0,X2) = X1)))),
% 0.91/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.91/0.85  
% 0.91/0.85  fof(f8,negated_conjecture,(
% 0.91/0.85    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(k6_relat_1(X1),X2) => (r1_tarski(X1,k2_relset_1(X1,X0,X2)) & k1_relset_1(X1,X0,X2) = X1)))),
% 0.91/0.85    inference(negated_conjecture,[],[f7])).
% 0.91/0.85  
% 0.91/0.85  fof(f19,plain,(
% 0.91/0.85    ? [X0,X1,X2] : (((~r1_tarski(X1,k2_relset_1(X1,X0,X2)) | k1_relset_1(X1,X0,X2) != X1) & r1_tarski(k6_relat_1(X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.91/0.85    inference(ennf_transformation,[],[f8])).
% 0.91/0.85  
% 0.91/0.85  fof(f20,plain,(
% 0.91/0.85    ? [X0,X1,X2] : ((~r1_tarski(X1,k2_relset_1(X1,X0,X2)) | k1_relset_1(X1,X0,X2) != X1) & r1_tarski(k6_relat_1(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.91/0.85    inference(flattening,[],[f19])).
% 0.91/0.85  
% 0.91/0.85  fof(f21,plain,(
% 0.91/0.85    ? [X0,X1,X2] : ((~r1_tarski(X1,k2_relset_1(X1,X0,X2)) | k1_relset_1(X1,X0,X2) != X1) & r1_tarski(k6_relat_1(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => ((~r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2)) | k1_relset_1(sK1,sK0,sK2) != sK1) & r1_tarski(k6_relat_1(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 0.91/0.85    introduced(choice_axiom,[])).
% 0.91/0.85  
% 0.91/0.85  fof(f22,plain,(
% 0.91/0.85    (~r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2)) | k1_relset_1(sK1,sK0,sK2) != sK1) & r1_tarski(k6_relat_1(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.91/0.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f21])).
% 0.91/0.85  
% 0.91/0.85  fof(f30,plain,(
% 0.91/0.85    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.91/0.85    inference(cnf_transformation,[],[f22])).
% 0.91/0.85  
% 0.91/0.85  fof(f5,axiom,(
% 0.91/0.85    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.91/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.91/0.85  
% 0.91/0.85  fof(f16,plain,(
% 0.91/0.85    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.91/0.85    inference(ennf_transformation,[],[f5])).
% 0.91/0.85  
% 0.91/0.85  fof(f27,plain,(
% 0.91/0.85    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.91/0.85    inference(cnf_transformation,[],[f16])).
% 0.91/0.85  
% 0.91/0.85  fof(f32,plain,(
% 0.91/0.85    ~r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2)) | k1_relset_1(sK1,sK0,sK2) != sK1),
% 0.91/0.85    inference(cnf_transformation,[],[f22])).
% 0.91/0.85  
% 0.91/0.85  fof(f31,plain,(
% 0.91/0.85    r1_tarski(k6_relat_1(sK1),sK2)),
% 0.91/0.85    inference(cnf_transformation,[],[f22])).
% 0.91/0.85  
% 0.91/0.85  fof(f6,axiom,(
% 0.91/0.85    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(k6_relat_1(X2),X3) => (r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3)))))),
% 0.91/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.91/0.85  
% 0.91/0.85  fof(f17,plain,(
% 0.91/0.85    ! [X0,X1,X2,X3] : (((r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3))) | ~r1_tarski(k6_relat_1(X2),X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.91/0.85    inference(ennf_transformation,[],[f6])).
% 0.91/0.85  
% 0.91/0.85  fof(f18,plain,(
% 0.91/0.85    ! [X0,X1,X2,X3] : ((r1_tarski(X2,k2_relset_1(X0,X1,X3)) & r1_tarski(X2,k1_relset_1(X0,X1,X3))) | ~r1_tarski(k6_relat_1(X2),X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.91/0.85    inference(flattening,[],[f17])).
% 0.91/0.85  
% 0.91/0.85  fof(f29,plain,(
% 0.91/0.85    ( ! [X2,X0,X3,X1] : (r1_tarski(X2,k2_relset_1(X0,X1,X3)) | ~r1_tarski(k6_relat_1(X2),X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.91/0.85    inference(cnf_transformation,[],[f18])).
% 0.91/0.85  
% 0.91/0.85  fof(f28,plain,(
% 0.91/0.85    ( ! [X2,X0,X3,X1] : (r1_tarski(X2,k1_relset_1(X0,X1,X3)) | ~r1_tarski(k6_relat_1(X2),X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.91/0.85    inference(cnf_transformation,[],[f18])).
% 0.91/0.85  
% 0.91/0.85  fof(f4,axiom,(
% 0.91/0.85    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.91/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.91/0.85  
% 0.91/0.85  fof(f9,plain,(
% 0.91/0.85    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.91/0.85    inference(pure_predicate_removal,[],[f4])).
% 0.91/0.85  
% 0.91/0.85  fof(f15,plain,(
% 0.91/0.85    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.91/0.85    inference(ennf_transformation,[],[f9])).
% 0.91/0.85  
% 0.91/0.85  fof(f26,plain,(
% 0.91/0.85    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.91/0.85    inference(cnf_transformation,[],[f15])).
% 0.91/0.85  
% 0.91/0.85  fof(f1,axiom,(
% 0.91/0.85    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.91/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.91/0.85  
% 0.91/0.85  fof(f10,plain,(
% 0.91/0.85    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.91/0.85    inference(ennf_transformation,[],[f1])).
% 0.91/0.85  
% 0.91/0.85  fof(f11,plain,(
% 0.91/0.85    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.91/0.85    inference(flattening,[],[f10])).
% 0.91/0.85  
% 0.91/0.85  fof(f23,plain,(
% 0.91/0.85    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.91/0.85    inference(cnf_transformation,[],[f11])).
% 0.91/0.85  
% 0.91/0.85  cnf(c_1,plain,
% 0.91/0.85      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 0.91/0.85      | ~ v1_relat_1(X1)
% 0.91/0.85      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 0.91/0.85      inference(cnf_transformation,[],[f24]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_2,plain,
% 0.91/0.85      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 0.91/0.85      inference(cnf_transformation,[],[f25]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_9,negated_conjecture,
% 0.91/0.85      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 0.91/0.85      inference(cnf_transformation,[],[f30]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_205,plain,
% 0.91/0.85      ( v1_relat_1(X0)
% 0.91/0.85      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.91/0.85      | sK2 != X0 ),
% 0.91/0.85      inference(resolution_lifted,[status(thm)],[c_2,c_9]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_206,plain,
% 0.91/0.85      ( v1_relat_1(sK2)
% 0.91/0.85      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 0.91/0.85      inference(unflattening,[status(thm)],[c_205]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_232,plain,
% 0.91/0.85      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 0.91/0.85      | k1_zfmisc_1(k2_zfmisc_1(X2,X3)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.91/0.85      | k1_relat_1(k7_relat_1(X1,X0)) = X0
% 0.91/0.85      | sK2 != X1 ),
% 0.91/0.85      inference(resolution_lifted,[status(thm)],[c_1,c_206]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_233,plain,
% 0.91/0.85      ( ~ r1_tarski(X0,k1_relat_1(sK2))
% 0.91/0.85      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.91/0.85      | k1_relat_1(k7_relat_1(sK2,X0)) = X0 ),
% 0.91/0.85      inference(unflattening,[status(thm)],[c_232]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_293,plain,
% 0.91/0.85      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.91/0.85      | ~ sP0_iProver_split ),
% 0.91/0.85      inference(splitting,
% 0.91/0.85                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 0.91/0.85                [c_233]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_440,plain,
% 0.91/0.85      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.91/0.85      | sP0_iProver_split != iProver_top ),
% 0.91/0.85      inference(predicate_to_equality,[status(thm)],[c_293]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_295,plain,
% 0.91/0.85      ( sP1_iProver_split | sP0_iProver_split ),
% 0.91/0.85      inference(splitting,
% 0.91/0.85                [splitting(split),new_symbols(definition,[])],
% 0.91/0.85                [c_233]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_317,plain,
% 0.91/0.85      ( sP1_iProver_split = iProver_top | sP0_iProver_split = iProver_top ),
% 0.91/0.85      inference(predicate_to_equality,[status(thm)],[c_295]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_321,plain,
% 0.91/0.85      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.91/0.85      | sP0_iProver_split != iProver_top ),
% 0.91/0.85      inference(predicate_to_equality,[status(thm)],[c_293]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_4,plain,
% 0.91/0.85      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.91/0.85      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 0.91/0.85      inference(cnf_transformation,[],[f27]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_196,plain,
% 0.91/0.85      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 0.91/0.85      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.91/0.85      | sK2 != X2 ),
% 0.91/0.85      inference(resolution_lifted,[status(thm)],[c_4,c_9]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_197,plain,
% 0.91/0.85      ( k1_relset_1(X0,X1,sK2) = k1_relat_1(sK2)
% 0.91/0.85      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 0.91/0.85      inference(unflattening,[status(thm)],[c_196]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_534,plain,
% 0.91/0.85      ( k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
% 0.91/0.85      inference(equality_resolution,[status(thm)],[c_197]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_7,negated_conjecture,
% 0.91/0.85      ( ~ r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2))
% 0.91/0.85      | k1_relset_1(sK1,sK0,sK2) != sK1 ),
% 0.91/0.85      inference(cnf_transformation,[],[f32]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_444,plain,
% 0.91/0.85      ( k1_relset_1(sK1,sK0,sK2) != sK1
% 0.91/0.85      | r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2)) != iProver_top ),
% 0.91/0.85      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_8,negated_conjecture,
% 0.91/0.85      ( r1_tarski(k6_relat_1(sK1),sK2) ),
% 0.91/0.85      inference(cnf_transformation,[],[f31]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_297,plain,( X0 = X0 ),theory(equality) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_500,plain,
% 0.91/0.85      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 0.91/0.85      inference(instantiation,[status(thm)],[c_297]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_5,plain,
% 0.91/0.85      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.91/0.85      | r1_tarski(X3,k2_relset_1(X1,X2,X0))
% 0.91/0.85      | ~ r1_tarski(k6_relat_1(X3),X0) ),
% 0.91/0.85      inference(cnf_transformation,[],[f29]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_181,plain,
% 0.91/0.85      ( r1_tarski(X0,k2_relset_1(X1,X2,X3))
% 0.91/0.85      | ~ r1_tarski(k6_relat_1(X0),X3)
% 0.91/0.85      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.91/0.85      | sK2 != X3 ),
% 0.91/0.85      inference(resolution_lifted,[status(thm)],[c_5,c_9]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_182,plain,
% 0.91/0.85      ( r1_tarski(X0,k2_relset_1(X1,X2,sK2))
% 0.91/0.85      | ~ r1_tarski(k6_relat_1(X0),sK2)
% 0.91/0.85      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 0.91/0.85      inference(unflattening,[status(thm)],[c_181]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_501,plain,
% 0.91/0.85      ( r1_tarski(X0,k2_relset_1(sK1,sK0,sK2))
% 0.91/0.85      | ~ r1_tarski(k6_relat_1(X0),sK2)
% 0.91/0.85      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 0.91/0.85      inference(instantiation,[status(thm)],[c_182]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_508,plain,
% 0.91/0.85      ( ~ r1_tarski(k6_relat_1(sK1),sK2)
% 0.91/0.85      | r1_tarski(sK1,k2_relset_1(sK1,sK0,sK2))
% 0.91/0.85      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 0.91/0.85      inference(instantiation,[status(thm)],[c_501]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_529,plain,
% 0.91/0.85      ( k1_relset_1(sK1,sK0,sK2) != sK1 ),
% 0.91/0.85      inference(global_propositional_subsumption,
% 0.91/0.85                [status(thm)],
% 0.91/0.85                [c_444,c_8,c_7,c_500,c_508]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_580,plain,
% 0.91/0.85      ( k1_relat_1(sK2) != sK1 ),
% 0.91/0.85      inference(demodulation,[status(thm)],[c_534,c_529]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_443,plain,
% 0.91/0.85      ( r1_tarski(k6_relat_1(sK1),sK2) = iProver_top ),
% 0.91/0.85      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_6,plain,
% 0.91/0.85      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.91/0.85      | r1_tarski(X3,k1_relset_1(X1,X2,X0))
% 0.91/0.85      | ~ r1_tarski(k6_relat_1(X3),X0) ),
% 0.91/0.85      inference(cnf_transformation,[],[f28]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_166,plain,
% 0.91/0.85      ( r1_tarski(X0,k1_relset_1(X1,X2,X3))
% 0.91/0.85      | ~ r1_tarski(k6_relat_1(X0),X3)
% 0.91/0.85      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.91/0.85      | sK2 != X3 ),
% 0.91/0.85      inference(resolution_lifted,[status(thm)],[c_6,c_9]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_167,plain,
% 0.91/0.85      ( r1_tarski(X0,k1_relset_1(X1,X2,sK2))
% 0.91/0.85      | ~ r1_tarski(k6_relat_1(X0),sK2)
% 0.91/0.85      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 0.91/0.85      inference(unflattening,[status(thm)],[c_166]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_442,plain,
% 0.91/0.85      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.91/0.85      | r1_tarski(X2,k1_relset_1(X0,X1,sK2)) = iProver_top
% 0.91/0.85      | r1_tarski(k6_relat_1(X2),sK2) != iProver_top ),
% 0.91/0.85      inference(predicate_to_equality,[status(thm)],[c_167]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_694,plain,
% 0.91/0.85      ( r1_tarski(X0,k1_relset_1(sK1,sK0,sK2)) = iProver_top
% 0.91/0.85      | r1_tarski(k6_relat_1(X0),sK2) != iProver_top ),
% 0.91/0.85      inference(equality_resolution,[status(thm)],[c_442]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_695,plain,
% 0.91/0.85      ( r1_tarski(X0,k1_relat_1(sK2)) = iProver_top
% 0.91/0.85      | r1_tarski(k6_relat_1(X0),sK2) != iProver_top ),
% 0.91/0.85      inference(light_normalisation,[status(thm)],[c_694,c_534]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_758,plain,
% 0.91/0.85      ( r1_tarski(sK1,k1_relat_1(sK2)) = iProver_top ),
% 0.91/0.85      inference(superposition,[status(thm)],[c_443,c_695]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_294,plain,
% 0.91/0.85      ( ~ r1_tarski(X0,k1_relat_1(sK2))
% 0.91/0.85      | k1_relat_1(k7_relat_1(sK2,X0)) = X0
% 0.91/0.85      | ~ sP1_iProver_split ),
% 0.91/0.85      inference(splitting,
% 0.91/0.85                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 0.91/0.85                [c_233]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_439,plain,
% 0.91/0.85      ( k1_relat_1(k7_relat_1(sK2,X0)) = X0
% 0.91/0.85      | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
% 0.91/0.85      | sP1_iProver_split != iProver_top ),
% 0.91/0.85      inference(predicate_to_equality,[status(thm)],[c_294]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_795,plain,
% 0.91/0.85      ( k1_relat_1(k7_relat_1(sK2,sK1)) = sK1
% 0.91/0.85      | sP1_iProver_split != iProver_top ),
% 0.91/0.85      inference(superposition,[status(thm)],[c_758,c_439]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_3,plain,
% 0.91/0.85      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v4_relat_1(X0,X1) ),
% 0.91/0.85      inference(cnf_transformation,[],[f26]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_0,plain,
% 0.91/0.85      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 0.91/0.85      inference(cnf_transformation,[],[f23]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_119,plain,
% 0.91/0.85      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.91/0.85      | ~ v1_relat_1(X0)
% 0.91/0.85      | k7_relat_1(X0,X1) = X0 ),
% 0.91/0.85      inference(resolution,[status(thm)],[c_3,c_0]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_123,plain,
% 0.91/0.85      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.91/0.85      | k7_relat_1(X0,X1) = X0 ),
% 0.91/0.85      inference(global_propositional_subsumption,
% 0.91/0.85                [status(thm)],
% 0.91/0.85                [c_119,c_3,c_2,c_0]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_157,plain,
% 0.91/0.85      ( k7_relat_1(X0,X1) = X0
% 0.91/0.85      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))
% 0.91/0.85      | sK2 != X0 ),
% 0.91/0.85      inference(resolution_lifted,[status(thm)],[c_123,c_9]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_158,plain,
% 0.91/0.85      ( k7_relat_1(sK2,X0) = sK2
% 0.91/0.85      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 0.91/0.85      inference(unflattening,[status(thm)],[c_157]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_516,plain,
% 0.91/0.85      ( k7_relat_1(sK2,sK1) = sK2 ),
% 0.91/0.85      inference(equality_resolution,[status(thm)],[c_158]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_796,plain,
% 0.91/0.85      ( k1_relat_1(sK2) = sK1 | sP1_iProver_split != iProver_top ),
% 0.91/0.85      inference(light_normalisation,[status(thm)],[c_795,c_516]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_850,plain,
% 0.91/0.85      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)) ),
% 0.91/0.85      inference(global_propositional_subsumption,
% 0.91/0.85                [status(thm)],
% 0.91/0.85                [c_440,c_317,c_321,c_580,c_796]) ).
% 0.91/0.85  
% 0.91/0.85  cnf(c_854,plain,
% 0.91/0.85      ( $false ),
% 0.91/0.85      inference(equality_resolution,[status(thm)],[c_850]) ).
% 0.91/0.85  
% 0.91/0.85  
% 0.91/0.85  % SZS output end CNFRefutation for theBenchmark.p
% 0.91/0.85  
% 0.91/0.85  ------                               Statistics
% 0.91/0.85  
% 0.91/0.85  ------ General
% 0.91/0.85  
% 0.91/0.85  abstr_ref_over_cycles:                  0
% 0.91/0.85  abstr_ref_under_cycles:                 0
% 0.91/0.85  gc_basic_clause_elim:                   0
% 0.91/0.85  forced_gc_time:                         0
% 0.91/0.85  parsing_time:                           0.009
% 0.91/0.85  unif_index_cands_time:                  0.
% 0.91/0.85  unif_index_add_time:                    0.
% 0.91/0.86  orderings_time:                         0.
% 0.91/0.86  out_proof_time:                         0.007
% 0.91/0.86  total_time:                             0.056
% 0.91/0.86  num_of_symbols:                         47
% 0.91/0.86  num_of_terms:                           800
% 0.91/0.86  
% 0.91/0.86  ------ Preprocessing
% 0.91/0.86  
% 0.91/0.86  num_of_splits:                          2
% 0.91/0.86  num_of_split_atoms:                     2
% 0.91/0.86  num_of_reused_defs:                     0
% 0.91/0.86  num_eq_ax_congr_red:                    7
% 0.91/0.86  num_of_sem_filtered_clauses:            1
% 0.91/0.86  num_of_subtypes:                        0
% 0.91/0.86  monotx_restored_types:                  0
% 0.91/0.86  sat_num_of_epr_types:                   0
% 0.91/0.86  sat_num_of_non_cyclic_types:            0
% 0.91/0.86  sat_guarded_non_collapsed_types:        0
% 0.91/0.86  num_pure_diseq_elim:                    0
% 0.91/0.86  simp_replaced_by:                       0
% 0.91/0.86  res_preprocessed:                       56
% 0.91/0.86  prep_upred:                             0
% 0.91/0.86  prep_unflattend:                        7
% 0.91/0.86  smt_new_axioms:                         0
% 0.91/0.86  pred_elim_cands:                        1
% 0.91/0.86  pred_elim:                              3
% 0.91/0.86  pred_elim_cl:                           3
% 0.91/0.86  pred_elim_cycles:                       6
% 0.91/0.86  merged_defs:                            0
% 0.91/0.86  merged_defs_ncl:                        0
% 0.91/0.86  bin_hyper_res:                          0
% 0.91/0.86  prep_cycles:                            4
% 0.91/0.86  pred_elim_time:                         0.002
% 0.91/0.86  splitting_time:                         0.
% 0.91/0.86  sem_filter_time:                        0.
% 0.91/0.86  monotx_time:                            0.
% 0.91/0.86  subtype_inf_time:                       0.
% 0.91/0.86  
% 0.91/0.86  ------ Problem properties
% 0.91/0.86  
% 0.91/0.86  clauses:                                9
% 0.91/0.86  conjectures:                            2
% 0.91/0.86  epr:                                    1
% 0.91/0.86  horn:                                   8
% 0.91/0.86  ground:                                 3
% 0.91/0.86  unary:                                  1
% 0.91/0.86  binary:                                 5
% 0.91/0.86  lits:                                   20
% 0.91/0.86  lits_eq:                                9
% 0.91/0.86  fd_pure:                                0
% 0.91/0.86  fd_pseudo:                              0
% 0.91/0.86  fd_cond:                                0
% 0.91/0.86  fd_pseudo_cond:                         0
% 0.91/0.86  ac_symbols:                             0
% 0.91/0.86  
% 0.91/0.86  ------ Propositional Solver
% 0.91/0.86  
% 0.91/0.86  prop_solver_calls:                      26
% 0.91/0.86  prop_fast_solver_calls:                 320
% 0.91/0.86  smt_solver_calls:                       0
% 0.91/0.86  smt_fast_solver_calls:                  0
% 0.91/0.86  prop_num_of_clauses:                    272
% 0.91/0.86  prop_preprocess_simplified:             1516
% 0.91/0.86  prop_fo_subsumed:                       4
% 0.91/0.86  prop_solver_time:                       0.
% 0.91/0.86  smt_solver_time:                        0.
% 0.91/0.86  smt_fast_solver_time:                   0.
% 0.91/0.86  prop_fast_solver_time:                  0.
% 0.91/0.86  prop_unsat_core_time:                   0.
% 0.91/0.86  
% 0.91/0.86  ------ QBF
% 0.91/0.86  
% 0.91/0.86  qbf_q_res:                              0
% 0.91/0.86  qbf_num_tautologies:                    0
% 0.91/0.86  qbf_prep_cycles:                        0
% 0.91/0.86  
% 0.91/0.86  ------ BMC1
% 0.91/0.86  
% 0.91/0.86  bmc1_current_bound:                     -1
% 0.91/0.86  bmc1_last_solved_bound:                 -1
% 0.91/0.86  bmc1_unsat_core_size:                   -1
% 0.91/0.86  bmc1_unsat_core_parents_size:           -1
% 0.91/0.86  bmc1_merge_next_fun:                    0
% 0.91/0.86  bmc1_unsat_core_clauses_time:           0.
% 0.91/0.86  
% 0.91/0.86  ------ Instantiation
% 0.91/0.86  
% 0.91/0.86  inst_num_of_clauses:                    106
% 0.91/0.86  inst_num_in_passive:                    12
% 0.91/0.86  inst_num_in_active:                     76
% 0.91/0.86  inst_num_in_unprocessed:                18
% 0.91/0.86  inst_num_of_loops:                      80
% 0.91/0.86  inst_num_of_learning_restarts:          0
% 0.91/0.86  inst_num_moves_active_passive:          1
% 0.91/0.86  inst_lit_activity:                      0
% 0.91/0.86  inst_lit_activity_moves:                0
% 0.91/0.86  inst_num_tautologies:                   0
% 0.91/0.86  inst_num_prop_implied:                  0
% 0.91/0.86  inst_num_existing_simplified:           0
% 0.91/0.86  inst_num_eq_res_simplified:             0
% 0.91/0.86  inst_num_child_elim:                    0
% 0.91/0.86  inst_num_of_dismatching_blockings:      5
% 0.91/0.86  inst_num_of_non_proper_insts:           81
% 0.91/0.86  inst_num_of_duplicates:                 0
% 0.91/0.86  inst_inst_num_from_inst_to_res:         0
% 0.91/0.86  inst_dismatching_checking_time:         0.
% 0.91/0.86  
% 0.91/0.86  ------ Resolution
% 0.91/0.86  
% 0.91/0.86  res_num_of_clauses:                     0
% 0.91/0.86  res_num_in_passive:                     0
% 0.91/0.86  res_num_in_active:                      0
% 0.91/0.86  res_num_of_loops:                       60
% 0.91/0.86  res_forward_subset_subsumed:            18
% 0.91/0.86  res_backward_subset_subsumed:           0
% 0.91/0.86  res_forward_subsumed:                   0
% 0.91/0.86  res_backward_subsumed:                  0
% 0.91/0.86  res_forward_subsumption_resolution:     0
% 0.91/0.86  res_backward_subsumption_resolution:    0
% 0.91/0.86  res_clause_to_clause_subsumption:       9
% 0.91/0.86  res_orphan_elimination:                 0
% 0.91/0.86  res_tautology_del:                      24
% 0.91/0.86  res_num_eq_res_simplified:              0
% 0.91/0.86  res_num_sel_changes:                    0
% 0.91/0.86  res_moves_from_active_to_pass:          0
% 0.91/0.86  
% 0.91/0.86  ------ Superposition
% 0.91/0.86  
% 0.91/0.86  sup_time_total:                         0.
% 0.91/0.86  sup_time_generating:                    0.
% 0.91/0.86  sup_time_sim_full:                      0.
% 0.91/0.86  sup_time_sim_immed:                     0.
% 0.91/0.86  
% 0.91/0.86  sup_num_of_clauses:                     14
% 0.91/0.86  sup_num_in_active:                      12
% 0.91/0.86  sup_num_in_passive:                     2
% 0.91/0.86  sup_num_of_loops:                       14
% 0.91/0.86  sup_fw_superposition:                   2
% 0.91/0.86  sup_bw_superposition:                   1
% 0.91/0.86  sup_immediate_simplified:               2
% 0.91/0.86  sup_given_eliminated:                   0
% 0.91/0.86  comparisons_done:                       0
% 0.91/0.86  comparisons_avoided:                    0
% 0.91/0.86  
% 0.91/0.86  ------ Simplifications
% 0.91/0.86  
% 0.91/0.86  
% 0.91/0.86  sim_fw_subset_subsumed:                 0
% 0.91/0.86  sim_bw_subset_subsumed:                 2
% 0.91/0.86  sim_fw_subsumed:                        0
% 0.91/0.86  sim_bw_subsumed:                        0
% 0.91/0.86  sim_fw_subsumption_res:                 0
% 0.91/0.86  sim_bw_subsumption_res:                 0
% 0.91/0.86  sim_tautology_del:                      0
% 0.91/0.86  sim_eq_tautology_del:                   0
% 0.91/0.86  sim_eq_res_simp:                        0
% 0.91/0.86  sim_fw_demodulated:                     0
% 0.91/0.86  sim_bw_demodulated:                     1
% 0.91/0.86  sim_light_normalised:                   2
% 0.91/0.86  sim_joinable_taut:                      0
% 0.91/0.86  sim_joinable_simp:                      0
% 0.91/0.86  sim_ac_normalised:                      0
% 0.91/0.86  sim_smt_subsumption:                    0
% 0.91/0.86  
%------------------------------------------------------------------------------
