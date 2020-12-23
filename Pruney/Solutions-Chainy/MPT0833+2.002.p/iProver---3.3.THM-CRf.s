%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:55:53 EST 2020

% Result     : Theorem 1.48s
% Output     : CNFRefutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 244 expanded)
%              Number of clauses        :   75 ( 106 expanded)
%              Number of leaves         :   14 (  45 expanded)
%              Depth                    :   15
%              Number of atoms          :  287 ( 698 expanded)
%              Number of equality atoms :  100 ( 134 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    6 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( r1_tarski(X1,X2)
       => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
       => ( r1_tarski(X1,X2)
         => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f30,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f37,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
   => ( ~ r2_relset_1(sK1,sK2,k6_relset_1(sK1,sK2,sK3,sK4),sK4)
      & r1_tarski(sK2,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ~ r2_relset_1(sK1,sK2,k6_relset_1(sK1,sK2,sK3,sK4),sK4)
    & r1_tarski(sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f31,f37])).

fof(f55,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f56,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f28])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f57,plain,(
    ~ r2_relset_1(sK1,sK2,k6_relset_1(sK1,sK2,sK3,sK4),sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_428,plain,
    ( r2_hidden(sK0(X0_46,X1_46),X0_46)
    | r1_tarski(X0_46,X1_46) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_751,plain,
    ( r2_hidden(sK0(X0_46,X1_46),X0_46) = iProver_top
    | r1_tarski(X0_46,X1_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_428])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_418,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_761,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_418])).

cnf(c_13,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_10,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_253,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_13,c_10])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_257,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_253,c_12])).

cnf(c_258,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_257])).

cnf(c_415,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
    | r1_tarski(k2_relat_1(X0_45),X1_46) ),
    inference(subtyping,[status(esa)],[c_258])).

cnf(c_765,plain,
    ( m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top
    | r1_tarski(k2_relat_1(X0_45),X1_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_415])).

cnf(c_1546,plain,
    ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_761,c_765])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_427,plain,
    ( ~ r2_hidden(X0_45,X0_46)
    | r2_hidden(X0_45,X1_46)
    | ~ r1_tarski(X0_46,X1_46) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_752,plain,
    ( r2_hidden(X0_45,X0_46) != iProver_top
    | r2_hidden(X0_45,X1_46) = iProver_top
    | r1_tarski(X0_46,X1_46) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_427])).

cnf(c_1595,plain,
    ( r2_hidden(X0_45,k2_relat_1(sK4)) != iProver_top
    | r2_hidden(X0_45,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1546,c_752])).

cnf(c_1701,plain,
    ( r2_hidden(sK0(k2_relat_1(sK4),X0_46),sK2) = iProver_top
    | r1_tarski(k2_relat_1(sK4),X0_46) = iProver_top ),
    inference(superposition,[status(thm)],[c_751,c_1595])).

cnf(c_17,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_419,negated_conjecture,
    ( r1_tarski(sK2,sK3) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_760,plain,
    ( r1_tarski(sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_419])).

cnf(c_1140,plain,
    ( r2_hidden(X0_45,sK3) = iProver_top
    | r2_hidden(X0_45,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_760,c_752])).

cnf(c_1708,plain,
    ( r2_hidden(sK0(k2_relat_1(sK4),X0_46),sK3) = iProver_top
    | r1_tarski(k2_relat_1(sK4),X0_46) = iProver_top ),
    inference(superposition,[status(thm)],[c_1701,c_1140])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_429,plain,
    ( ~ r2_hidden(sK0(X0_46,X1_46),X1_46)
    | r1_tarski(X0_46,X1_46) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_750,plain,
    ( r2_hidden(sK0(X0_46,X1_46),X1_46) != iProver_top
    | r1_tarski(X0_46,X1_46) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_429])).

cnf(c_1804,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1708,c_750])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k6_relset_1(X1,X2,X3,X0) = k8_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_420,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
    | k6_relset_1(X0_46,X1_46,X2_46,X0_45) = k8_relat_1(X2_46,X0_45) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_759,plain,
    ( k6_relset_1(X0_46,X1_46,X2_46,X0_45) = k8_relat_1(X2_46,X0_45)
    | m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_420])).

cnf(c_1417,plain,
    ( k6_relset_1(sK1,sK2,X0_46,sK4) = k8_relat_1(X0_46,sK4) ),
    inference(superposition,[status(thm)],[c_761,c_759])).

cnf(c_15,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_16,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK2,k6_relset_1(sK1,sK2,sK3,sK4),sK4) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_234,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k6_relset_1(sK1,sK2,sK3,sK4) != X3
    | sK4 != X3
    | sK2 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_16])).

cnf(c_235,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(k6_relset_1(sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | sK4 != k6_relset_1(sK1,sK2,sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_234])).

cnf(c_416,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(k6_relset_1(sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | sK4 != k6_relset_1(sK1,sK2,sK3,sK4) ),
    inference(subtyping,[status(esa)],[c_235])).

cnf(c_431,plain,
    ( ~ m1_subset_1(k6_relset_1(sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | sP0_iProver_split
    | sK4 != k6_relset_1(sK1,sK2,sK3,sK4) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_416])).

cnf(c_763,plain,
    ( sK4 != k6_relset_1(sK1,sK2,sK3,sK4)
    | m1_subset_1(k6_relset_1(sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_431])).

cnf(c_430,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_416])).

cnf(c_764,plain,
    ( m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_430])).

cnf(c_829,plain,
    ( k6_relset_1(sK1,sK2,sK3,sK4) != sK4
    | m1_subset_1(k6_relset_1(sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_763,c_764])).

cnf(c_1469,plain,
    ( k8_relat_1(sK3,sK4) != sK4
    | m1_subset_1(k8_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1417,c_829])).

cnf(c_433,plain,
    ( X0_45 = X0_45 ),
    theory(equality)).

cnf(c_449,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_433])).

cnf(c_476,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ sP0_iProver_split ),
    inference(instantiation,[status(thm)],[c_430])).

cnf(c_517,plain,
    ( ~ m1_subset_1(k6_relset_1(sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | sK4 != k6_relset_1(sK1,sK2,sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_431,c_18,c_476])).

cnf(c_434,plain,
    ( X0_46 = X0_46 ),
    theory(equality)).

cnf(c_918,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_434])).

cnf(c_435,plain,
    ( X0_45 != X1_45
    | X2_45 != X1_45
    | X2_45 = X0_45 ),
    theory(equality)).

cnf(c_898,plain,
    ( k6_relset_1(sK1,sK2,sK3,sK4) != X0_45
    | sK4 != X0_45
    | sK4 = k6_relset_1(sK1,sK2,sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_435])).

cnf(c_934,plain,
    ( k6_relset_1(sK1,sK2,sK3,sK4) != k8_relat_1(sK3,sK4)
    | sK4 = k6_relset_1(sK1,sK2,sK3,sK4)
    | sK4 != k8_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_898])).

cnf(c_884,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k6_relset_1(sK1,sK2,X0_46,sK4) = k8_relat_1(X0_46,sK4) ),
    inference(instantiation,[status(thm)],[c_420])).

cnf(c_935,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k6_relset_1(sK1,sK2,sK3,sK4) = k8_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_884])).

cnf(c_939,plain,
    ( k8_relat_1(sK3,sK4) != X0_45
    | sK4 != X0_45
    | sK4 = k8_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_435])).

cnf(c_940,plain,
    ( k8_relat_1(sK3,sK4) != sK4
    | sK4 = k8_relat_1(sK3,sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_939])).

cnf(c_929,plain,
    ( X0_45 != X1_45
    | k6_relset_1(sK1,sK2,sK3,sK4) != X1_45
    | k6_relset_1(sK1,sK2,sK3,sK4) = X0_45 ),
    inference(instantiation,[status(thm)],[c_435])).

cnf(c_1091,plain,
    ( X0_45 != k8_relat_1(sK3,sK4)
    | k6_relset_1(sK1,sK2,sK3,sK4) = X0_45
    | k6_relset_1(sK1,sK2,sK3,sK4) != k8_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_929])).

cnf(c_1092,plain,
    ( k6_relset_1(sK1,sK2,sK3,sK4) != k8_relat_1(sK3,sK4)
    | k6_relset_1(sK1,sK2,sK3,sK4) = sK4
    | sK4 != k8_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1091])).

cnf(c_440,plain,
    ( ~ m1_subset_1(X0_45,X0_46)
    | m1_subset_1(X1_45,X1_46)
    | X1_46 != X0_46
    | X1_45 != X0_45 ),
    theory(equality)).

cnf(c_879,plain,
    ( m1_subset_1(X0_45,X0_46)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | X0_46 != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | X0_45 != sK4 ),
    inference(instantiation,[status(thm)],[c_440])).

cnf(c_921,plain,
    ( m1_subset_1(X0_45,k1_zfmisc_1(X0_46))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_zfmisc_1(X0_46) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | X0_45 != sK4 ),
    inference(instantiation,[status(thm)],[c_879])).

cnf(c_1185,plain,
    ( m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | X0_45 != sK4 ),
    inference(instantiation,[status(thm)],[c_921])).

cnf(c_1382,plain,
    ( m1_subset_1(k6_relset_1(sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
    | k6_relset_1(sK1,sK2,sK3,sK4) != sK4 ),
    inference(instantiation,[status(thm)],[c_1185])).

cnf(c_1540,plain,
    ( k8_relat_1(sK3,sK4) != sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1469,c_18,c_449,c_517,c_918,c_934,c_935,c_940,c_1092,c_1382])).

cnf(c_11,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k8_relat_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_422,plain,
    ( ~ r1_tarski(k2_relat_1(X0_45),X0_46)
    | ~ v1_relat_1(X0_45)
    | k8_relat_1(X0_46,X0_45) = X0_45 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1009,plain,
    ( ~ r1_tarski(k2_relat_1(sK4),sK3)
    | ~ v1_relat_1(sK4)
    | k8_relat_1(sK3,sK4) = sK4 ),
    inference(instantiation,[status(thm)],[c_422])).

cnf(c_1010,plain,
    ( k8_relat_1(sK3,sK4) = sK4
    | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1009])).

cnf(c_421,plain,
    ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
    | v1_relat_1(X0_45) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_869,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_421])).

cnf(c_870,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_869])).

cnf(c_19,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1804,c_1540,c_1010,c_870,c_19])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:47:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.48/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.48/1.00  
% 1.48/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.48/1.00  
% 1.48/1.00  ------  iProver source info
% 1.48/1.00  
% 1.48/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.48/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.48/1.00  git: non_committed_changes: false
% 1.48/1.00  git: last_make_outside_of_git: false
% 1.48/1.00  
% 1.48/1.00  ------ 
% 1.48/1.00  
% 1.48/1.00  ------ Input Options
% 1.48/1.00  
% 1.48/1.00  --out_options                           all
% 1.48/1.00  --tptp_safe_out                         true
% 1.48/1.00  --problem_path                          ""
% 1.48/1.00  --include_path                          ""
% 1.48/1.00  --clausifier                            res/vclausify_rel
% 1.48/1.00  --clausifier_options                    --mode clausify
% 1.48/1.00  --stdin                                 false
% 1.48/1.00  --stats_out                             all
% 1.48/1.00  
% 1.48/1.00  ------ General Options
% 1.48/1.00  
% 1.48/1.00  --fof                                   false
% 1.48/1.00  --time_out_real                         305.
% 1.48/1.00  --time_out_virtual                      -1.
% 1.48/1.00  --symbol_type_check                     false
% 1.48/1.00  --clausify_out                          false
% 1.48/1.00  --sig_cnt_out                           false
% 1.48/1.00  --trig_cnt_out                          false
% 1.48/1.00  --trig_cnt_out_tolerance                1.
% 1.48/1.00  --trig_cnt_out_sk_spl                   false
% 1.48/1.00  --abstr_cl_out                          false
% 1.48/1.00  
% 1.48/1.00  ------ Global Options
% 1.48/1.00  
% 1.48/1.00  --schedule                              default
% 1.48/1.00  --add_important_lit                     false
% 1.48/1.00  --prop_solver_per_cl                    1000
% 1.48/1.00  --min_unsat_core                        false
% 1.48/1.00  --soft_assumptions                      false
% 1.48/1.00  --soft_lemma_size                       3
% 1.48/1.00  --prop_impl_unit_size                   0
% 1.48/1.00  --prop_impl_unit                        []
% 1.48/1.00  --share_sel_clauses                     true
% 1.48/1.00  --reset_solvers                         false
% 1.48/1.00  --bc_imp_inh                            [conj_cone]
% 1.48/1.00  --conj_cone_tolerance                   3.
% 1.48/1.00  --extra_neg_conj                        none
% 1.48/1.00  --large_theory_mode                     true
% 1.48/1.00  --prolific_symb_bound                   200
% 1.48/1.00  --lt_threshold                          2000
% 1.48/1.00  --clause_weak_htbl                      true
% 1.48/1.00  --gc_record_bc_elim                     false
% 1.48/1.00  
% 1.48/1.00  ------ Preprocessing Options
% 1.48/1.00  
% 1.48/1.00  --preprocessing_flag                    true
% 1.48/1.00  --time_out_prep_mult                    0.1
% 1.48/1.00  --splitting_mode                        input
% 1.48/1.00  --splitting_grd                         true
% 1.48/1.00  --splitting_cvd                         false
% 1.48/1.00  --splitting_cvd_svl                     false
% 1.48/1.00  --splitting_nvd                         32
% 1.48/1.00  --sub_typing                            true
% 1.48/1.00  --prep_gs_sim                           true
% 1.48/1.00  --prep_unflatten                        true
% 1.48/1.00  --prep_res_sim                          true
% 1.48/1.00  --prep_upred                            true
% 1.48/1.00  --prep_sem_filter                       exhaustive
% 1.48/1.00  --prep_sem_filter_out                   false
% 1.48/1.00  --pred_elim                             true
% 1.48/1.00  --res_sim_input                         true
% 1.48/1.00  --eq_ax_congr_red                       true
% 1.48/1.00  --pure_diseq_elim                       true
% 1.48/1.00  --brand_transform                       false
% 1.48/1.00  --non_eq_to_eq                          false
% 1.48/1.00  --prep_def_merge                        true
% 1.48/1.00  --prep_def_merge_prop_impl              false
% 1.48/1.00  --prep_def_merge_mbd                    true
% 1.48/1.00  --prep_def_merge_tr_red                 false
% 1.48/1.00  --prep_def_merge_tr_cl                  false
% 1.48/1.00  --smt_preprocessing                     true
% 1.48/1.00  --smt_ac_axioms                         fast
% 1.48/1.00  --preprocessed_out                      false
% 1.48/1.00  --preprocessed_stats                    false
% 1.48/1.00  
% 1.48/1.00  ------ Abstraction refinement Options
% 1.48/1.00  
% 1.48/1.00  --abstr_ref                             []
% 1.48/1.00  --abstr_ref_prep                        false
% 1.48/1.00  --abstr_ref_until_sat                   false
% 1.48/1.00  --abstr_ref_sig_restrict                funpre
% 1.48/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.48/1.00  --abstr_ref_under                       []
% 1.48/1.00  
% 1.48/1.00  ------ SAT Options
% 1.48/1.00  
% 1.48/1.00  --sat_mode                              false
% 1.48/1.00  --sat_fm_restart_options                ""
% 1.48/1.00  --sat_gr_def                            false
% 1.48/1.00  --sat_epr_types                         true
% 1.48/1.00  --sat_non_cyclic_types                  false
% 1.48/1.00  --sat_finite_models                     false
% 1.48/1.00  --sat_fm_lemmas                         false
% 1.48/1.00  --sat_fm_prep                           false
% 1.48/1.00  --sat_fm_uc_incr                        true
% 1.48/1.00  --sat_out_model                         small
% 1.48/1.00  --sat_out_clauses                       false
% 1.48/1.00  
% 1.48/1.00  ------ QBF Options
% 1.48/1.00  
% 1.48/1.00  --qbf_mode                              false
% 1.48/1.00  --qbf_elim_univ                         false
% 1.48/1.00  --qbf_dom_inst                          none
% 1.48/1.00  --qbf_dom_pre_inst                      false
% 1.48/1.00  --qbf_sk_in                             false
% 1.48/1.00  --qbf_pred_elim                         true
% 1.48/1.00  --qbf_split                             512
% 1.48/1.00  
% 1.48/1.00  ------ BMC1 Options
% 1.48/1.00  
% 1.48/1.00  --bmc1_incremental                      false
% 1.48/1.00  --bmc1_axioms                           reachable_all
% 1.48/1.00  --bmc1_min_bound                        0
% 1.48/1.00  --bmc1_max_bound                        -1
% 1.48/1.00  --bmc1_max_bound_default                -1
% 1.48/1.00  --bmc1_symbol_reachability              true
% 1.48/1.00  --bmc1_property_lemmas                  false
% 1.48/1.00  --bmc1_k_induction                      false
% 1.48/1.00  --bmc1_non_equiv_states                 false
% 1.48/1.00  --bmc1_deadlock                         false
% 1.48/1.00  --bmc1_ucm                              false
% 1.48/1.00  --bmc1_add_unsat_core                   none
% 1.48/1.00  --bmc1_unsat_core_children              false
% 1.48/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.48/1.00  --bmc1_out_stat                         full
% 1.48/1.00  --bmc1_ground_init                      false
% 1.48/1.00  --bmc1_pre_inst_next_state              false
% 1.48/1.00  --bmc1_pre_inst_state                   false
% 1.48/1.00  --bmc1_pre_inst_reach_state             false
% 1.48/1.00  --bmc1_out_unsat_core                   false
% 1.48/1.00  --bmc1_aig_witness_out                  false
% 1.48/1.00  --bmc1_verbose                          false
% 1.48/1.00  --bmc1_dump_clauses_tptp                false
% 1.48/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.48/1.00  --bmc1_dump_file                        -
% 1.48/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.48/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.48/1.00  --bmc1_ucm_extend_mode                  1
% 1.48/1.00  --bmc1_ucm_init_mode                    2
% 1.48/1.00  --bmc1_ucm_cone_mode                    none
% 1.48/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.48/1.00  --bmc1_ucm_relax_model                  4
% 1.48/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.48/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.48/1.00  --bmc1_ucm_layered_model                none
% 1.48/1.00  --bmc1_ucm_max_lemma_size               10
% 1.48/1.00  
% 1.48/1.00  ------ AIG Options
% 1.48/1.00  
% 1.48/1.00  --aig_mode                              false
% 1.48/1.00  
% 1.48/1.00  ------ Instantiation Options
% 1.48/1.00  
% 1.48/1.00  --instantiation_flag                    true
% 1.48/1.00  --inst_sos_flag                         false
% 1.48/1.00  --inst_sos_phase                        true
% 1.48/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.48/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.48/1.00  --inst_lit_sel_side                     num_symb
% 1.48/1.00  --inst_solver_per_active                1400
% 1.48/1.00  --inst_solver_calls_frac                1.
% 1.48/1.00  --inst_passive_queue_type               priority_queues
% 1.48/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.48/1.00  --inst_passive_queues_freq              [25;2]
% 1.48/1.00  --inst_dismatching                      true
% 1.48/1.00  --inst_eager_unprocessed_to_passive     true
% 1.48/1.00  --inst_prop_sim_given                   true
% 1.48/1.00  --inst_prop_sim_new                     false
% 1.48/1.00  --inst_subs_new                         false
% 1.48/1.00  --inst_eq_res_simp                      false
% 1.48/1.00  --inst_subs_given                       false
% 1.48/1.00  --inst_orphan_elimination               true
% 1.48/1.00  --inst_learning_loop_flag               true
% 1.48/1.00  --inst_learning_start                   3000
% 1.48/1.00  --inst_learning_factor                  2
% 1.48/1.00  --inst_start_prop_sim_after_learn       3
% 1.48/1.00  --inst_sel_renew                        solver
% 1.48/1.00  --inst_lit_activity_flag                true
% 1.48/1.00  --inst_restr_to_given                   false
% 1.48/1.00  --inst_activity_threshold               500
% 1.48/1.00  --inst_out_proof                        true
% 1.48/1.00  
% 1.48/1.00  ------ Resolution Options
% 1.48/1.00  
% 1.48/1.00  --resolution_flag                       true
% 1.48/1.00  --res_lit_sel                           adaptive
% 1.48/1.00  --res_lit_sel_side                      none
% 1.48/1.00  --res_ordering                          kbo
% 1.48/1.00  --res_to_prop_solver                    active
% 1.48/1.00  --res_prop_simpl_new                    false
% 1.48/1.00  --res_prop_simpl_given                  true
% 1.48/1.00  --res_passive_queue_type                priority_queues
% 1.48/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.48/1.00  --res_passive_queues_freq               [15;5]
% 1.48/1.00  --res_forward_subs                      full
% 1.48/1.00  --res_backward_subs                     full
% 1.48/1.00  --res_forward_subs_resolution           true
% 1.48/1.00  --res_backward_subs_resolution          true
% 1.48/1.00  --res_orphan_elimination                true
% 1.48/1.00  --res_time_limit                        2.
% 1.48/1.00  --res_out_proof                         true
% 1.48/1.00  
% 1.48/1.00  ------ Superposition Options
% 1.48/1.00  
% 1.48/1.00  --superposition_flag                    true
% 1.48/1.00  --sup_passive_queue_type                priority_queues
% 1.48/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.48/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.48/1.00  --demod_completeness_check              fast
% 1.48/1.00  --demod_use_ground                      true
% 1.48/1.00  --sup_to_prop_solver                    passive
% 1.48/1.00  --sup_prop_simpl_new                    true
% 1.48/1.00  --sup_prop_simpl_given                  true
% 1.48/1.00  --sup_fun_splitting                     false
% 1.48/1.00  --sup_smt_interval                      50000
% 1.48/1.00  
% 1.48/1.00  ------ Superposition Simplification Setup
% 1.48/1.00  
% 1.48/1.00  --sup_indices_passive                   []
% 1.48/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.48/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.48/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.48/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.48/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.48/1.00  --sup_full_bw                           [BwDemod]
% 1.48/1.00  --sup_immed_triv                        [TrivRules]
% 1.48/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.48/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.48/1.00  --sup_immed_bw_main                     []
% 1.48/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.48/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.48/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.48/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.48/1.00  
% 1.48/1.00  ------ Combination Options
% 1.48/1.00  
% 1.48/1.00  --comb_res_mult                         3
% 1.48/1.00  --comb_sup_mult                         2
% 1.48/1.00  --comb_inst_mult                        10
% 1.48/1.00  
% 1.48/1.00  ------ Debug Options
% 1.48/1.00  
% 1.48/1.00  --dbg_backtrace                         false
% 1.48/1.00  --dbg_dump_prop_clauses                 false
% 1.48/1.00  --dbg_dump_prop_clauses_file            -
% 1.48/1.00  --dbg_out_stat                          false
% 1.48/1.00  ------ Parsing...
% 1.48/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.48/1.00  
% 1.48/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 1.48/1.00  
% 1.48/1.00  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.48/1.00  
% 1.48/1.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.48/1.00  ------ Proving...
% 1.48/1.00  ------ Problem Properties 
% 1.48/1.00  
% 1.48/1.00  
% 1.48/1.00  clauses                                 16
% 1.48/1.00  conjectures                             2
% 1.48/1.00  EPR                                     3
% 1.48/1.00  Horn                                    15
% 1.48/1.00  unary                                   2
% 1.48/1.00  binary                                  11
% 1.48/1.00  lits                                    33
% 1.48/1.00  lits eq                                 3
% 1.48/1.00  fd_pure                                 0
% 1.48/1.00  fd_pseudo                               0
% 1.48/1.00  fd_cond                                 0
% 1.48/1.00  fd_pseudo_cond                          0
% 1.48/1.00  AC symbols                              0
% 1.48/1.00  
% 1.48/1.00  ------ Schedule dynamic 5 is on 
% 1.48/1.00  
% 1.48/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.48/1.00  
% 1.48/1.00  
% 1.48/1.00  ------ 
% 1.48/1.00  Current options:
% 1.48/1.00  ------ 
% 1.48/1.00  
% 1.48/1.00  ------ Input Options
% 1.48/1.00  
% 1.48/1.00  --out_options                           all
% 1.48/1.00  --tptp_safe_out                         true
% 1.48/1.00  --problem_path                          ""
% 1.48/1.00  --include_path                          ""
% 1.48/1.00  --clausifier                            res/vclausify_rel
% 1.48/1.00  --clausifier_options                    --mode clausify
% 1.48/1.00  --stdin                                 false
% 1.48/1.00  --stats_out                             all
% 1.48/1.00  
% 1.48/1.00  ------ General Options
% 1.48/1.00  
% 1.48/1.00  --fof                                   false
% 1.48/1.00  --time_out_real                         305.
% 1.48/1.00  --time_out_virtual                      -1.
% 1.48/1.00  --symbol_type_check                     false
% 1.48/1.00  --clausify_out                          false
% 1.48/1.00  --sig_cnt_out                           false
% 1.48/1.00  --trig_cnt_out                          false
% 1.48/1.00  --trig_cnt_out_tolerance                1.
% 1.48/1.00  --trig_cnt_out_sk_spl                   false
% 1.48/1.00  --abstr_cl_out                          false
% 1.48/1.00  
% 1.48/1.00  ------ Global Options
% 1.48/1.00  
% 1.48/1.00  --schedule                              default
% 1.48/1.00  --add_important_lit                     false
% 1.48/1.00  --prop_solver_per_cl                    1000
% 1.48/1.00  --min_unsat_core                        false
% 1.48/1.00  --soft_assumptions                      false
% 1.48/1.00  --soft_lemma_size                       3
% 1.48/1.00  --prop_impl_unit_size                   0
% 1.48/1.00  --prop_impl_unit                        []
% 1.48/1.00  --share_sel_clauses                     true
% 1.48/1.00  --reset_solvers                         false
% 1.48/1.00  --bc_imp_inh                            [conj_cone]
% 1.48/1.00  --conj_cone_tolerance                   3.
% 1.48/1.00  --extra_neg_conj                        none
% 1.48/1.00  --large_theory_mode                     true
% 1.48/1.00  --prolific_symb_bound                   200
% 1.48/1.00  --lt_threshold                          2000
% 1.48/1.00  --clause_weak_htbl                      true
% 1.48/1.00  --gc_record_bc_elim                     false
% 1.48/1.00  
% 1.48/1.00  ------ Preprocessing Options
% 1.48/1.00  
% 1.48/1.00  --preprocessing_flag                    true
% 1.48/1.00  --time_out_prep_mult                    0.1
% 1.48/1.00  --splitting_mode                        input
% 1.48/1.00  --splitting_grd                         true
% 1.48/1.00  --splitting_cvd                         false
% 1.48/1.00  --splitting_cvd_svl                     false
% 1.48/1.00  --splitting_nvd                         32
% 1.48/1.00  --sub_typing                            true
% 1.48/1.00  --prep_gs_sim                           true
% 1.48/1.00  --prep_unflatten                        true
% 1.48/1.00  --prep_res_sim                          true
% 1.48/1.00  --prep_upred                            true
% 1.48/1.00  --prep_sem_filter                       exhaustive
% 1.48/1.00  --prep_sem_filter_out                   false
% 1.48/1.00  --pred_elim                             true
% 1.48/1.00  --res_sim_input                         true
% 1.48/1.00  --eq_ax_congr_red                       true
% 1.48/1.00  --pure_diseq_elim                       true
% 1.48/1.00  --brand_transform                       false
% 1.48/1.00  --non_eq_to_eq                          false
% 1.48/1.00  --prep_def_merge                        true
% 1.48/1.00  --prep_def_merge_prop_impl              false
% 1.48/1.00  --prep_def_merge_mbd                    true
% 1.48/1.00  --prep_def_merge_tr_red                 false
% 1.48/1.00  --prep_def_merge_tr_cl                  false
% 1.48/1.00  --smt_preprocessing                     true
% 1.48/1.00  --smt_ac_axioms                         fast
% 1.48/1.00  --preprocessed_out                      false
% 1.48/1.00  --preprocessed_stats                    false
% 1.48/1.00  
% 1.48/1.00  ------ Abstraction refinement Options
% 1.48/1.00  
% 1.48/1.00  --abstr_ref                             []
% 1.48/1.00  --abstr_ref_prep                        false
% 1.48/1.00  --abstr_ref_until_sat                   false
% 1.48/1.00  --abstr_ref_sig_restrict                funpre
% 1.48/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.48/1.00  --abstr_ref_under                       []
% 1.48/1.00  
% 1.48/1.00  ------ SAT Options
% 1.48/1.00  
% 1.48/1.00  --sat_mode                              false
% 1.48/1.00  --sat_fm_restart_options                ""
% 1.48/1.00  --sat_gr_def                            false
% 1.48/1.00  --sat_epr_types                         true
% 1.48/1.00  --sat_non_cyclic_types                  false
% 1.48/1.00  --sat_finite_models                     false
% 1.48/1.00  --sat_fm_lemmas                         false
% 1.48/1.00  --sat_fm_prep                           false
% 1.48/1.00  --sat_fm_uc_incr                        true
% 1.48/1.00  --sat_out_model                         small
% 1.48/1.00  --sat_out_clauses                       false
% 1.48/1.00  
% 1.48/1.00  ------ QBF Options
% 1.48/1.00  
% 1.48/1.00  --qbf_mode                              false
% 1.48/1.00  --qbf_elim_univ                         false
% 1.48/1.00  --qbf_dom_inst                          none
% 1.48/1.00  --qbf_dom_pre_inst                      false
% 1.48/1.00  --qbf_sk_in                             false
% 1.48/1.00  --qbf_pred_elim                         true
% 1.48/1.00  --qbf_split                             512
% 1.48/1.00  
% 1.48/1.00  ------ BMC1 Options
% 1.48/1.00  
% 1.48/1.00  --bmc1_incremental                      false
% 1.48/1.00  --bmc1_axioms                           reachable_all
% 1.48/1.00  --bmc1_min_bound                        0
% 1.48/1.00  --bmc1_max_bound                        -1
% 1.48/1.00  --bmc1_max_bound_default                -1
% 1.48/1.00  --bmc1_symbol_reachability              true
% 1.48/1.00  --bmc1_property_lemmas                  false
% 1.48/1.00  --bmc1_k_induction                      false
% 1.48/1.00  --bmc1_non_equiv_states                 false
% 1.48/1.00  --bmc1_deadlock                         false
% 1.48/1.00  --bmc1_ucm                              false
% 1.48/1.00  --bmc1_add_unsat_core                   none
% 1.48/1.00  --bmc1_unsat_core_children              false
% 1.48/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.48/1.00  --bmc1_out_stat                         full
% 1.48/1.00  --bmc1_ground_init                      false
% 1.48/1.00  --bmc1_pre_inst_next_state              false
% 1.48/1.00  --bmc1_pre_inst_state                   false
% 1.48/1.00  --bmc1_pre_inst_reach_state             false
% 1.48/1.00  --bmc1_out_unsat_core                   false
% 1.48/1.00  --bmc1_aig_witness_out                  false
% 1.48/1.00  --bmc1_verbose                          false
% 1.48/1.00  --bmc1_dump_clauses_tptp                false
% 1.48/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.48/1.00  --bmc1_dump_file                        -
% 1.48/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.48/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.48/1.00  --bmc1_ucm_extend_mode                  1
% 1.48/1.00  --bmc1_ucm_init_mode                    2
% 1.48/1.00  --bmc1_ucm_cone_mode                    none
% 1.48/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.48/1.00  --bmc1_ucm_relax_model                  4
% 1.48/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.48/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.48/1.00  --bmc1_ucm_layered_model                none
% 1.48/1.00  --bmc1_ucm_max_lemma_size               10
% 1.48/1.00  
% 1.48/1.00  ------ AIG Options
% 1.48/1.00  
% 1.48/1.00  --aig_mode                              false
% 1.48/1.00  
% 1.48/1.00  ------ Instantiation Options
% 1.48/1.00  
% 1.48/1.00  --instantiation_flag                    true
% 1.48/1.00  --inst_sos_flag                         false
% 1.48/1.00  --inst_sos_phase                        true
% 1.48/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.48/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.48/1.00  --inst_lit_sel_side                     none
% 1.48/1.00  --inst_solver_per_active                1400
% 1.48/1.00  --inst_solver_calls_frac                1.
% 1.48/1.00  --inst_passive_queue_type               priority_queues
% 1.48/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.48/1.00  --inst_passive_queues_freq              [25;2]
% 1.48/1.00  --inst_dismatching                      true
% 1.48/1.00  --inst_eager_unprocessed_to_passive     true
% 1.48/1.00  --inst_prop_sim_given                   true
% 1.48/1.00  --inst_prop_sim_new                     false
% 1.48/1.00  --inst_subs_new                         false
% 1.48/1.00  --inst_eq_res_simp                      false
% 1.48/1.00  --inst_subs_given                       false
% 1.48/1.00  --inst_orphan_elimination               true
% 1.48/1.00  --inst_learning_loop_flag               true
% 1.48/1.00  --inst_learning_start                   3000
% 1.48/1.00  --inst_learning_factor                  2
% 1.48/1.00  --inst_start_prop_sim_after_learn       3
% 1.48/1.00  --inst_sel_renew                        solver
% 1.48/1.00  --inst_lit_activity_flag                true
% 1.48/1.00  --inst_restr_to_given                   false
% 1.48/1.00  --inst_activity_threshold               500
% 1.48/1.00  --inst_out_proof                        true
% 1.48/1.00  
% 1.48/1.00  ------ Resolution Options
% 1.48/1.00  
% 1.48/1.00  --resolution_flag                       false
% 1.48/1.00  --res_lit_sel                           adaptive
% 1.48/1.00  --res_lit_sel_side                      none
% 1.48/1.00  --res_ordering                          kbo
% 1.48/1.01  --res_to_prop_solver                    active
% 1.48/1.01  --res_prop_simpl_new                    false
% 1.48/1.01  --res_prop_simpl_given                  true
% 1.48/1.01  --res_passive_queue_type                priority_queues
% 1.48/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.48/1.01  --res_passive_queues_freq               [15;5]
% 1.48/1.01  --res_forward_subs                      full
% 1.48/1.01  --res_backward_subs                     full
% 1.48/1.01  --res_forward_subs_resolution           true
% 1.48/1.01  --res_backward_subs_resolution          true
% 1.48/1.01  --res_orphan_elimination                true
% 1.48/1.01  --res_time_limit                        2.
% 1.48/1.01  --res_out_proof                         true
% 1.48/1.01  
% 1.48/1.01  ------ Superposition Options
% 1.48/1.01  
% 1.48/1.01  --superposition_flag                    true
% 1.48/1.01  --sup_passive_queue_type                priority_queues
% 1.48/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.48/1.01  --sup_passive_queues_freq               [8;1;4]
% 1.48/1.01  --demod_completeness_check              fast
% 1.48/1.01  --demod_use_ground                      true
% 1.48/1.01  --sup_to_prop_solver                    passive
% 1.48/1.01  --sup_prop_simpl_new                    true
% 1.48/1.01  --sup_prop_simpl_given                  true
% 1.48/1.01  --sup_fun_splitting                     false
% 1.48/1.01  --sup_smt_interval                      50000
% 1.48/1.01  
% 1.48/1.01  ------ Superposition Simplification Setup
% 1.48/1.01  
% 1.48/1.01  --sup_indices_passive                   []
% 1.48/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.48/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.48/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.48/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 1.48/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.48/1.01  --sup_full_bw                           [BwDemod]
% 1.48/1.01  --sup_immed_triv                        [TrivRules]
% 1.48/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.48/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.48/1.01  --sup_immed_bw_main                     []
% 1.48/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.48/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.48/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.48/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.48/1.01  
% 1.48/1.01  ------ Combination Options
% 1.48/1.01  
% 1.48/1.01  --comb_res_mult                         3
% 1.48/1.01  --comb_sup_mult                         2
% 1.48/1.01  --comb_inst_mult                        10
% 1.48/1.01  
% 1.48/1.01  ------ Debug Options
% 1.48/1.01  
% 1.48/1.01  --dbg_backtrace                         false
% 1.48/1.01  --dbg_dump_prop_clauses                 false
% 1.48/1.01  --dbg_dump_prop_clauses_file            -
% 1.48/1.01  --dbg_out_stat                          false
% 1.48/1.01  
% 1.48/1.01  
% 1.48/1.01  
% 1.48/1.01  
% 1.48/1.01  ------ Proving...
% 1.48/1.01  
% 1.48/1.01  
% 1.48/1.01  % SZS status Theorem for theBenchmark.p
% 1.48/1.01  
% 1.48/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 1.48/1.01  
% 1.48/1.01  fof(f1,axiom,(
% 1.48/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.48/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.48/1.01  
% 1.48/1.01  fof(f16,plain,(
% 1.48/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.48/1.01    inference(ennf_transformation,[],[f1])).
% 1.48/1.01  
% 1.48/1.01  fof(f32,plain,(
% 1.48/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.48/1.01    inference(nnf_transformation,[],[f16])).
% 1.48/1.01  
% 1.48/1.01  fof(f33,plain,(
% 1.48/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.48/1.01    inference(rectify,[],[f32])).
% 1.48/1.01  
% 1.48/1.01  fof(f34,plain,(
% 1.48/1.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 1.48/1.01    introduced(choice_axiom,[])).
% 1.48/1.01  
% 1.48/1.01  fof(f35,plain,(
% 1.48/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.48/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 1.48/1.01  
% 1.48/1.01  fof(f40,plain,(
% 1.48/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 1.48/1.01    inference(cnf_transformation,[],[f35])).
% 1.48/1.01  
% 1.48/1.01  fof(f13,conjecture,(
% 1.48/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(X1,X2) => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)))),
% 1.48/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.48/1.01  
% 1.48/1.01  fof(f14,negated_conjecture,(
% 1.48/1.01    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (r1_tarski(X1,X2) => r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3)))),
% 1.48/1.01    inference(negated_conjecture,[],[f13])).
% 1.48/1.01  
% 1.48/1.01  fof(f30,plain,(
% 1.48/1.01    ? [X0,X1,X2,X3] : ((~r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) & r1_tarski(X1,X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/1.01    inference(ennf_transformation,[],[f14])).
% 1.48/1.01  
% 1.48/1.01  fof(f31,plain,(
% 1.48/1.01    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/1.01    inference(flattening,[],[f30])).
% 1.48/1.01  
% 1.48/1.01  fof(f37,plain,(
% 1.48/1.01    ? [X0,X1,X2,X3] : (~r2_relset_1(X0,X1,k6_relset_1(X0,X1,X2,X3),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (~r2_relset_1(sK1,sK2,k6_relset_1(sK1,sK2,sK3,sK4),sK4) & r1_tarski(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))))),
% 1.48/1.01    introduced(choice_axiom,[])).
% 1.48/1.01  
% 1.48/1.01  fof(f38,plain,(
% 1.48/1.01    ~r2_relset_1(sK1,sK2,k6_relset_1(sK1,sK2,sK3,sK4),sK4) & r1_tarski(sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.48/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f31,f37])).
% 1.48/1.01  
% 1.48/1.01  fof(f55,plain,(
% 1.48/1.01    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.48/1.01    inference(cnf_transformation,[],[f38])).
% 1.48/1.01  
% 1.48/1.01  fof(f10,axiom,(
% 1.48/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.48/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.48/1.01  
% 1.48/1.01  fof(f15,plain,(
% 1.48/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 1.48/1.01    inference(pure_predicate_removal,[],[f10])).
% 1.48/1.01  
% 1.48/1.01  fof(f26,plain,(
% 1.48/1.01    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/1.01    inference(ennf_transformation,[],[f15])).
% 1.48/1.01  
% 1.48/1.01  fof(f52,plain,(
% 1.48/1.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.48/1.01    inference(cnf_transformation,[],[f26])).
% 1.48/1.01  
% 1.48/1.01  fof(f7,axiom,(
% 1.48/1.01    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.48/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.48/1.01  
% 1.48/1.01  fof(f22,plain,(
% 1.48/1.01    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.48/1.01    inference(ennf_transformation,[],[f7])).
% 1.48/1.01  
% 1.48/1.01  fof(f36,plain,(
% 1.48/1.01    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.48/1.01    inference(nnf_transformation,[],[f22])).
% 1.48/1.01  
% 1.48/1.01  fof(f48,plain,(
% 1.48/1.01    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.48/1.01    inference(cnf_transformation,[],[f36])).
% 1.48/1.01  
% 1.48/1.01  fof(f9,axiom,(
% 1.48/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.48/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.48/1.01  
% 1.48/1.01  fof(f25,plain,(
% 1.48/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/1.01    inference(ennf_transformation,[],[f9])).
% 1.48/1.01  
% 1.48/1.01  fof(f51,plain,(
% 1.48/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.48/1.01    inference(cnf_transformation,[],[f25])).
% 1.48/1.01  
% 1.48/1.01  fof(f39,plain,(
% 1.48/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.48/1.01    inference(cnf_transformation,[],[f35])).
% 1.48/1.01  
% 1.48/1.01  fof(f56,plain,(
% 1.48/1.01    r1_tarski(sK2,sK3)),
% 1.48/1.01    inference(cnf_transformation,[],[f38])).
% 1.48/1.01  
% 1.48/1.01  fof(f41,plain,(
% 1.48/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 1.48/1.01    inference(cnf_transformation,[],[f35])).
% 1.48/1.01  
% 1.48/1.01  fof(f11,axiom,(
% 1.48/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3))),
% 1.48/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.48/1.01  
% 1.48/1.01  fof(f27,plain,(
% 1.48/1.01    ! [X0,X1,X2,X3] : (k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/1.01    inference(ennf_transformation,[],[f11])).
% 1.48/1.01  
% 1.48/1.01  fof(f53,plain,(
% 1.48/1.01    ( ! [X2,X0,X3,X1] : (k8_relat_1(X2,X3) = k6_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.48/1.01    inference(cnf_transformation,[],[f27])).
% 1.48/1.01  
% 1.48/1.01  fof(f12,axiom,(
% 1.48/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 1.48/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.48/1.01  
% 1.48/1.01  fof(f28,plain,(
% 1.48/1.01    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.48/1.01    inference(ennf_transformation,[],[f12])).
% 1.48/1.01  
% 1.48/1.01  fof(f29,plain,(
% 1.48/1.01    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/1.01    inference(flattening,[],[f28])).
% 1.48/1.01  
% 1.48/1.01  fof(f54,plain,(
% 1.48/1.01    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.48/1.01    inference(cnf_transformation,[],[f29])).
% 1.48/1.01  
% 1.48/1.01  fof(f57,plain,(
% 1.48/1.01    ~r2_relset_1(sK1,sK2,k6_relset_1(sK1,sK2,sK3,sK4),sK4)),
% 1.48/1.01    inference(cnf_transformation,[],[f38])).
% 1.48/1.01  
% 1.48/1.01  fof(f8,axiom,(
% 1.48/1.01    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 1.48/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.48/1.01  
% 1.48/1.01  fof(f23,plain,(
% 1.48/1.01    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.48/1.01    inference(ennf_transformation,[],[f8])).
% 1.48/1.01  
% 1.48/1.01  fof(f24,plain,(
% 1.48/1.01    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.48/1.01    inference(flattening,[],[f23])).
% 1.48/1.01  
% 1.48/1.01  fof(f50,plain,(
% 1.48/1.01    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.48/1.01    inference(cnf_transformation,[],[f24])).
% 1.48/1.01  
% 1.48/1.01  cnf(c_1,plain,
% 1.48/1.01      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 1.48/1.01      inference(cnf_transformation,[],[f40]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_428,plain,
% 1.48/1.01      ( r2_hidden(sK0(X0_46,X1_46),X0_46) | r1_tarski(X0_46,X1_46) ),
% 1.48/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_751,plain,
% 1.48/1.01      ( r2_hidden(sK0(X0_46,X1_46),X0_46) = iProver_top
% 1.48/1.01      | r1_tarski(X0_46,X1_46) = iProver_top ),
% 1.48/1.01      inference(predicate_to_equality,[status(thm)],[c_428]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_18,negated_conjecture,
% 1.48/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 1.48/1.01      inference(cnf_transformation,[],[f55]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_418,negated_conjecture,
% 1.48/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 1.48/1.01      inference(subtyping,[status(esa)],[c_18]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_761,plain,
% 1.48/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 1.48/1.01      inference(predicate_to_equality,[status(thm)],[c_418]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_13,plain,
% 1.48/1.01      ( v5_relat_1(X0,X1)
% 1.48/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 1.48/1.01      inference(cnf_transformation,[],[f52]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_10,plain,
% 1.48/1.01      ( ~ v5_relat_1(X0,X1)
% 1.48/1.01      | r1_tarski(k2_relat_1(X0),X1)
% 1.48/1.01      | ~ v1_relat_1(X0) ),
% 1.48/1.01      inference(cnf_transformation,[],[f48]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_253,plain,
% 1.48/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.48/1.01      | r1_tarski(k2_relat_1(X0),X2)
% 1.48/1.01      | ~ v1_relat_1(X0) ),
% 1.48/1.01      inference(resolution,[status(thm)],[c_13,c_10]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_12,plain,
% 1.48/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.48/1.01      | v1_relat_1(X0) ),
% 1.48/1.01      inference(cnf_transformation,[],[f51]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_257,plain,
% 1.48/1.01      ( r1_tarski(k2_relat_1(X0),X2)
% 1.48/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.48/1.01      inference(global_propositional_subsumption,
% 1.48/1.01                [status(thm)],
% 1.48/1.01                [c_253,c_12]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_258,plain,
% 1.48/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.48/1.01      | r1_tarski(k2_relat_1(X0),X2) ),
% 1.48/1.01      inference(renaming,[status(thm)],[c_257]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_415,plain,
% 1.48/1.01      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
% 1.48/1.01      | r1_tarski(k2_relat_1(X0_45),X1_46) ),
% 1.48/1.01      inference(subtyping,[status(esa)],[c_258]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_765,plain,
% 1.48/1.01      ( m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top
% 1.48/1.01      | r1_tarski(k2_relat_1(X0_45),X1_46) = iProver_top ),
% 1.48/1.01      inference(predicate_to_equality,[status(thm)],[c_415]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_1546,plain,
% 1.48/1.01      ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
% 1.48/1.01      inference(superposition,[status(thm)],[c_761,c_765]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_2,plain,
% 1.48/1.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 1.48/1.01      inference(cnf_transformation,[],[f39]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_427,plain,
% 1.48/1.01      ( ~ r2_hidden(X0_45,X0_46)
% 1.48/1.01      | r2_hidden(X0_45,X1_46)
% 1.48/1.01      | ~ r1_tarski(X0_46,X1_46) ),
% 1.48/1.01      inference(subtyping,[status(esa)],[c_2]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_752,plain,
% 1.48/1.01      ( r2_hidden(X0_45,X0_46) != iProver_top
% 1.48/1.01      | r2_hidden(X0_45,X1_46) = iProver_top
% 1.48/1.01      | r1_tarski(X0_46,X1_46) != iProver_top ),
% 1.48/1.01      inference(predicate_to_equality,[status(thm)],[c_427]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_1595,plain,
% 1.48/1.01      ( r2_hidden(X0_45,k2_relat_1(sK4)) != iProver_top
% 1.48/1.01      | r2_hidden(X0_45,sK2) = iProver_top ),
% 1.48/1.01      inference(superposition,[status(thm)],[c_1546,c_752]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_1701,plain,
% 1.48/1.01      ( r2_hidden(sK0(k2_relat_1(sK4),X0_46),sK2) = iProver_top
% 1.48/1.01      | r1_tarski(k2_relat_1(sK4),X0_46) = iProver_top ),
% 1.48/1.01      inference(superposition,[status(thm)],[c_751,c_1595]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_17,negated_conjecture,
% 1.48/1.01      ( r1_tarski(sK2,sK3) ),
% 1.48/1.01      inference(cnf_transformation,[],[f56]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_419,negated_conjecture,
% 1.48/1.01      ( r1_tarski(sK2,sK3) ),
% 1.48/1.01      inference(subtyping,[status(esa)],[c_17]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_760,plain,
% 1.48/1.01      ( r1_tarski(sK2,sK3) = iProver_top ),
% 1.48/1.01      inference(predicate_to_equality,[status(thm)],[c_419]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_1140,plain,
% 1.48/1.01      ( r2_hidden(X0_45,sK3) = iProver_top
% 1.48/1.01      | r2_hidden(X0_45,sK2) != iProver_top ),
% 1.48/1.01      inference(superposition,[status(thm)],[c_760,c_752]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_1708,plain,
% 1.48/1.01      ( r2_hidden(sK0(k2_relat_1(sK4),X0_46),sK3) = iProver_top
% 1.48/1.01      | r1_tarski(k2_relat_1(sK4),X0_46) = iProver_top ),
% 1.48/1.01      inference(superposition,[status(thm)],[c_1701,c_1140]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_0,plain,
% 1.48/1.01      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 1.48/1.01      inference(cnf_transformation,[],[f41]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_429,plain,
% 1.48/1.01      ( ~ r2_hidden(sK0(X0_46,X1_46),X1_46) | r1_tarski(X0_46,X1_46) ),
% 1.48/1.01      inference(subtyping,[status(esa)],[c_0]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_750,plain,
% 1.48/1.01      ( r2_hidden(sK0(X0_46,X1_46),X1_46) != iProver_top
% 1.48/1.01      | r1_tarski(X0_46,X1_46) = iProver_top ),
% 1.48/1.01      inference(predicate_to_equality,[status(thm)],[c_429]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_1804,plain,
% 1.48/1.01      ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
% 1.48/1.01      inference(superposition,[status(thm)],[c_1708,c_750]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_14,plain,
% 1.48/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.48/1.01      | k6_relset_1(X1,X2,X3,X0) = k8_relat_1(X3,X0) ),
% 1.48/1.01      inference(cnf_transformation,[],[f53]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_420,plain,
% 1.48/1.01      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
% 1.48/1.01      | k6_relset_1(X0_46,X1_46,X2_46,X0_45) = k8_relat_1(X2_46,X0_45) ),
% 1.48/1.01      inference(subtyping,[status(esa)],[c_14]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_759,plain,
% 1.48/1.01      ( k6_relset_1(X0_46,X1_46,X2_46,X0_45) = k8_relat_1(X2_46,X0_45)
% 1.48/1.01      | m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46))) != iProver_top ),
% 1.48/1.01      inference(predicate_to_equality,[status(thm)],[c_420]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_1417,plain,
% 1.48/1.01      ( k6_relset_1(sK1,sK2,X0_46,sK4) = k8_relat_1(X0_46,sK4) ),
% 1.48/1.01      inference(superposition,[status(thm)],[c_761,c_759]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_15,plain,
% 1.48/1.01      ( r2_relset_1(X0,X1,X2,X2)
% 1.48/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.48/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 1.48/1.01      inference(cnf_transformation,[],[f54]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_16,negated_conjecture,
% 1.48/1.01      ( ~ r2_relset_1(sK1,sK2,k6_relset_1(sK1,sK2,sK3,sK4),sK4) ),
% 1.48/1.01      inference(cnf_transformation,[],[f57]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_234,plain,
% 1.48/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.48/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.48/1.01      | k6_relset_1(sK1,sK2,sK3,sK4) != X3
% 1.48/1.01      | sK4 != X3
% 1.48/1.01      | sK2 != X2
% 1.48/1.01      | sK1 != X1 ),
% 1.48/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_16]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_235,plain,
% 1.48/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 1.48/1.01      | ~ m1_subset_1(k6_relset_1(sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 1.48/1.01      | sK4 != k6_relset_1(sK1,sK2,sK3,sK4) ),
% 1.48/1.01      inference(unflattening,[status(thm)],[c_234]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_416,plain,
% 1.48/1.01      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 1.48/1.01      | ~ m1_subset_1(k6_relset_1(sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 1.48/1.01      | sK4 != k6_relset_1(sK1,sK2,sK3,sK4) ),
% 1.48/1.01      inference(subtyping,[status(esa)],[c_235]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_431,plain,
% 1.48/1.01      ( ~ m1_subset_1(k6_relset_1(sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 1.48/1.01      | sP0_iProver_split
% 1.48/1.01      | sK4 != k6_relset_1(sK1,sK2,sK3,sK4) ),
% 1.48/1.01      inference(splitting,
% 1.48/1.01                [splitting(split),new_symbols(definition,[])],
% 1.48/1.01                [c_416]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_763,plain,
% 1.48/1.01      ( sK4 != k6_relset_1(sK1,sK2,sK3,sK4)
% 1.48/1.01      | m1_subset_1(k6_relset_1(sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 1.48/1.01      | sP0_iProver_split = iProver_top ),
% 1.48/1.01      inference(predicate_to_equality,[status(thm)],[c_431]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_430,plain,
% 1.48/1.01      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 1.48/1.01      | ~ sP0_iProver_split ),
% 1.48/1.01      inference(splitting,
% 1.48/1.01                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.48/1.01                [c_416]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_764,plain,
% 1.48/1.01      ( m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 1.48/1.01      | sP0_iProver_split != iProver_top ),
% 1.48/1.01      inference(predicate_to_equality,[status(thm)],[c_430]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_829,plain,
% 1.48/1.01      ( k6_relset_1(sK1,sK2,sK3,sK4) != sK4
% 1.48/1.01      | m1_subset_1(k6_relset_1(sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 1.48/1.01      inference(forward_subsumption_resolution,
% 1.48/1.01                [status(thm)],
% 1.48/1.01                [c_763,c_764]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_1469,plain,
% 1.48/1.01      ( k8_relat_1(sK3,sK4) != sK4
% 1.48/1.01      | m1_subset_1(k8_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 1.48/1.01      inference(demodulation,[status(thm)],[c_1417,c_829]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_433,plain,( X0_45 = X0_45 ),theory(equality) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_449,plain,
% 1.48/1.01      ( sK4 = sK4 ),
% 1.48/1.01      inference(instantiation,[status(thm)],[c_433]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_476,plain,
% 1.48/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 1.48/1.01      | ~ sP0_iProver_split ),
% 1.48/1.01      inference(instantiation,[status(thm)],[c_430]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_517,plain,
% 1.48/1.01      ( ~ m1_subset_1(k6_relset_1(sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 1.48/1.01      | sK4 != k6_relset_1(sK1,sK2,sK3,sK4) ),
% 1.48/1.01      inference(global_propositional_subsumption,
% 1.48/1.01                [status(thm)],
% 1.48/1.01                [c_431,c_18,c_476]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_434,plain,( X0_46 = X0_46 ),theory(equality) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_918,plain,
% 1.48/1.01      ( k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) = k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) ),
% 1.48/1.01      inference(instantiation,[status(thm)],[c_434]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_435,plain,
% 1.48/1.01      ( X0_45 != X1_45 | X2_45 != X1_45 | X2_45 = X0_45 ),
% 1.48/1.01      theory(equality) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_898,plain,
% 1.48/1.01      ( k6_relset_1(sK1,sK2,sK3,sK4) != X0_45
% 1.48/1.01      | sK4 != X0_45
% 1.48/1.01      | sK4 = k6_relset_1(sK1,sK2,sK3,sK4) ),
% 1.48/1.01      inference(instantiation,[status(thm)],[c_435]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_934,plain,
% 1.48/1.01      ( k6_relset_1(sK1,sK2,sK3,sK4) != k8_relat_1(sK3,sK4)
% 1.48/1.01      | sK4 = k6_relset_1(sK1,sK2,sK3,sK4)
% 1.48/1.01      | sK4 != k8_relat_1(sK3,sK4) ),
% 1.48/1.01      inference(instantiation,[status(thm)],[c_898]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_884,plain,
% 1.48/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 1.48/1.01      | k6_relset_1(sK1,sK2,X0_46,sK4) = k8_relat_1(X0_46,sK4) ),
% 1.48/1.01      inference(instantiation,[status(thm)],[c_420]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_935,plain,
% 1.48/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 1.48/1.01      | k6_relset_1(sK1,sK2,sK3,sK4) = k8_relat_1(sK3,sK4) ),
% 1.48/1.01      inference(instantiation,[status(thm)],[c_884]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_939,plain,
% 1.48/1.01      ( k8_relat_1(sK3,sK4) != X0_45
% 1.48/1.01      | sK4 != X0_45
% 1.48/1.01      | sK4 = k8_relat_1(sK3,sK4) ),
% 1.48/1.01      inference(instantiation,[status(thm)],[c_435]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_940,plain,
% 1.48/1.01      ( k8_relat_1(sK3,sK4) != sK4
% 1.48/1.01      | sK4 = k8_relat_1(sK3,sK4)
% 1.48/1.01      | sK4 != sK4 ),
% 1.48/1.01      inference(instantiation,[status(thm)],[c_939]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_929,plain,
% 1.48/1.01      ( X0_45 != X1_45
% 1.48/1.01      | k6_relset_1(sK1,sK2,sK3,sK4) != X1_45
% 1.48/1.01      | k6_relset_1(sK1,sK2,sK3,sK4) = X0_45 ),
% 1.48/1.01      inference(instantiation,[status(thm)],[c_435]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_1091,plain,
% 1.48/1.01      ( X0_45 != k8_relat_1(sK3,sK4)
% 1.48/1.01      | k6_relset_1(sK1,sK2,sK3,sK4) = X0_45
% 1.48/1.01      | k6_relset_1(sK1,sK2,sK3,sK4) != k8_relat_1(sK3,sK4) ),
% 1.48/1.01      inference(instantiation,[status(thm)],[c_929]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_1092,plain,
% 1.48/1.01      ( k6_relset_1(sK1,sK2,sK3,sK4) != k8_relat_1(sK3,sK4)
% 1.48/1.01      | k6_relset_1(sK1,sK2,sK3,sK4) = sK4
% 1.48/1.01      | sK4 != k8_relat_1(sK3,sK4) ),
% 1.48/1.01      inference(instantiation,[status(thm)],[c_1091]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_440,plain,
% 1.48/1.01      ( ~ m1_subset_1(X0_45,X0_46)
% 1.48/1.01      | m1_subset_1(X1_45,X1_46)
% 1.48/1.01      | X1_46 != X0_46
% 1.48/1.01      | X1_45 != X0_45 ),
% 1.48/1.01      theory(equality) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_879,plain,
% 1.48/1.01      ( m1_subset_1(X0_45,X0_46)
% 1.48/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 1.48/1.01      | X0_46 != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 1.48/1.01      | X0_45 != sK4 ),
% 1.48/1.01      inference(instantiation,[status(thm)],[c_440]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_921,plain,
% 1.48/1.01      ( m1_subset_1(X0_45,k1_zfmisc_1(X0_46))
% 1.48/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 1.48/1.01      | k1_zfmisc_1(X0_46) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 1.48/1.01      | X0_45 != sK4 ),
% 1.48/1.01      inference(instantiation,[status(thm)],[c_879]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_1185,plain,
% 1.48/1.01      ( m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
% 1.48/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 1.48/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 1.48/1.01      | X0_45 != sK4 ),
% 1.48/1.01      inference(instantiation,[status(thm)],[c_921]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_1382,plain,
% 1.48/1.01      ( m1_subset_1(k6_relset_1(sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 1.48/1.01      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 1.48/1.01      | k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)) != k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))
% 1.48/1.01      | k6_relset_1(sK1,sK2,sK3,sK4) != sK4 ),
% 1.48/1.01      inference(instantiation,[status(thm)],[c_1185]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_1540,plain,
% 1.48/1.01      ( k8_relat_1(sK3,sK4) != sK4 ),
% 1.48/1.01      inference(global_propositional_subsumption,
% 1.48/1.01                [status(thm)],
% 1.48/1.01                [c_1469,c_18,c_449,c_517,c_918,c_934,c_935,c_940,c_1092,
% 1.48/1.01                 c_1382]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_11,plain,
% 1.48/1.01      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 1.48/1.01      | ~ v1_relat_1(X0)
% 1.48/1.01      | k8_relat_1(X1,X0) = X0 ),
% 1.48/1.01      inference(cnf_transformation,[],[f50]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_422,plain,
% 1.48/1.01      ( ~ r1_tarski(k2_relat_1(X0_45),X0_46)
% 1.48/1.01      | ~ v1_relat_1(X0_45)
% 1.48/1.01      | k8_relat_1(X0_46,X0_45) = X0_45 ),
% 1.48/1.01      inference(subtyping,[status(esa)],[c_11]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_1009,plain,
% 1.48/1.01      ( ~ r1_tarski(k2_relat_1(sK4),sK3)
% 1.48/1.01      | ~ v1_relat_1(sK4)
% 1.48/1.01      | k8_relat_1(sK3,sK4) = sK4 ),
% 1.48/1.01      inference(instantiation,[status(thm)],[c_422]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_1010,plain,
% 1.48/1.01      ( k8_relat_1(sK3,sK4) = sK4
% 1.48/1.01      | r1_tarski(k2_relat_1(sK4),sK3) != iProver_top
% 1.48/1.01      | v1_relat_1(sK4) != iProver_top ),
% 1.48/1.01      inference(predicate_to_equality,[status(thm)],[c_1009]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_421,plain,
% 1.48/1.01      ( ~ m1_subset_1(X0_45,k1_zfmisc_1(k2_zfmisc_1(X0_46,X1_46)))
% 1.48/1.01      | v1_relat_1(X0_45) ),
% 1.48/1.01      inference(subtyping,[status(esa)],[c_12]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_869,plain,
% 1.48/1.01      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 1.48/1.01      | v1_relat_1(sK4) ),
% 1.48/1.01      inference(instantiation,[status(thm)],[c_421]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_870,plain,
% 1.48/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 1.48/1.01      | v1_relat_1(sK4) = iProver_top ),
% 1.48/1.01      inference(predicate_to_equality,[status(thm)],[c_869]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(c_19,plain,
% 1.48/1.01      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 1.48/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.48/1.01  
% 1.48/1.01  cnf(contradiction,plain,
% 1.48/1.01      ( $false ),
% 1.48/1.01      inference(minisat,[status(thm)],[c_1804,c_1540,c_1010,c_870,c_19]) ).
% 1.48/1.01  
% 1.48/1.01  
% 1.48/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 1.48/1.01  
% 1.48/1.01  ------                               Statistics
% 1.48/1.01  
% 1.48/1.01  ------ General
% 1.48/1.01  
% 1.48/1.01  abstr_ref_over_cycles:                  0
% 1.48/1.01  abstr_ref_under_cycles:                 0
% 1.48/1.01  gc_basic_clause_elim:                   0
% 1.48/1.01  forced_gc_time:                         0
% 1.48/1.01  parsing_time:                           0.009
% 1.48/1.01  unif_index_cands_time:                  0.
% 1.48/1.01  unif_index_add_time:                    0.
% 1.48/1.01  orderings_time:                         0.
% 1.48/1.01  out_proof_time:                         0.012
% 1.48/1.01  total_time:                             0.09
% 1.48/1.01  num_of_symbols:                         51
% 1.48/1.01  num_of_terms:                           1572
% 1.48/1.01  
% 1.48/1.01  ------ Preprocessing
% 1.48/1.01  
% 1.48/1.01  num_of_splits:                          1
% 1.48/1.01  num_of_split_atoms:                     1
% 1.48/1.01  num_of_reused_defs:                     0
% 1.48/1.01  num_eq_ax_congr_red:                    21
% 1.48/1.01  num_of_sem_filtered_clauses:            2
% 1.48/1.01  num_of_subtypes:                        2
% 1.48/1.01  monotx_restored_types:                  1
% 1.48/1.01  sat_num_of_epr_types:                   0
% 1.48/1.01  sat_num_of_non_cyclic_types:            0
% 1.48/1.01  sat_guarded_non_collapsed_types:        0
% 1.48/1.01  num_pure_diseq_elim:                    0
% 1.48/1.01  simp_replaced_by:                       0
% 1.48/1.01  res_preprocessed:                       84
% 1.48/1.01  prep_upred:                             0
% 1.48/1.01  prep_unflattend:                        4
% 1.48/1.01  smt_new_axioms:                         0
% 1.48/1.01  pred_elim_cands:                        4
% 1.48/1.01  pred_elim:                              3
% 1.48/1.01  pred_elim_cl:                           4
% 1.48/1.01  pred_elim_cycles:                       5
% 1.48/1.01  merged_defs:                            0
% 1.48/1.01  merged_defs_ncl:                        0
% 1.48/1.01  bin_hyper_res:                          0
% 1.48/1.01  prep_cycles:                            4
% 1.48/1.01  pred_elim_time:                         0.002
% 1.48/1.01  splitting_time:                         0.
% 1.48/1.01  sem_filter_time:                        0.
% 1.48/1.01  monotx_time:                            0.001
% 1.48/1.01  subtype_inf_time:                       0.001
% 1.48/1.01  
% 1.48/1.01  ------ Problem properties
% 1.48/1.01  
% 1.48/1.01  clauses:                                16
% 1.48/1.01  conjectures:                            2
% 1.48/1.01  epr:                                    3
% 1.48/1.01  horn:                                   15
% 1.48/1.01  ground:                                 3
% 1.48/1.01  unary:                                  2
% 1.48/1.01  binary:                                 11
% 1.48/1.01  lits:                                   33
% 1.48/1.01  lits_eq:                                3
% 1.48/1.01  fd_pure:                                0
% 1.48/1.01  fd_pseudo:                              0
% 1.48/1.01  fd_cond:                                0
% 1.48/1.01  fd_pseudo_cond:                         0
% 1.48/1.01  ac_symbols:                             0
% 1.48/1.01  
% 1.48/1.01  ------ Propositional Solver
% 1.48/1.01  
% 1.48/1.01  prop_solver_calls:                      28
% 1.48/1.01  prop_fast_solver_calls:                 458
% 1.48/1.01  smt_solver_calls:                       0
% 1.48/1.01  smt_fast_solver_calls:                  0
% 1.48/1.01  prop_num_of_clauses:                    571
% 1.48/1.01  prop_preprocess_simplified:             2974
% 1.48/1.01  prop_fo_subsumed:                       6
% 1.48/1.01  prop_solver_time:                       0.
% 1.48/1.01  smt_solver_time:                        0.
% 1.48/1.01  smt_fast_solver_time:                   0.
% 1.48/1.01  prop_fast_solver_time:                  0.
% 1.48/1.01  prop_unsat_core_time:                   0.
% 1.48/1.01  
% 1.48/1.01  ------ QBF
% 1.48/1.01  
% 1.48/1.01  qbf_q_res:                              0
% 1.48/1.01  qbf_num_tautologies:                    0
% 1.48/1.01  qbf_prep_cycles:                        0
% 1.48/1.01  
% 1.48/1.01  ------ BMC1
% 1.48/1.01  
% 1.48/1.01  bmc1_current_bound:                     -1
% 1.48/1.01  bmc1_last_solved_bound:                 -1
% 1.48/1.01  bmc1_unsat_core_size:                   -1
% 1.48/1.01  bmc1_unsat_core_parents_size:           -1
% 1.48/1.01  bmc1_merge_next_fun:                    0
% 1.48/1.01  bmc1_unsat_core_clauses_time:           0.
% 1.48/1.01  
% 1.48/1.01  ------ Instantiation
% 1.48/1.01  
% 1.48/1.01  inst_num_of_clauses:                    162
% 1.48/1.01  inst_num_in_passive:                    22
% 1.48/1.01  inst_num_in_active:                     117
% 1.48/1.01  inst_num_in_unprocessed:                23
% 1.48/1.01  inst_num_of_loops:                      170
% 1.48/1.01  inst_num_of_learning_restarts:          0
% 1.48/1.01  inst_num_moves_active_passive:          49
% 1.48/1.01  inst_lit_activity:                      0
% 1.48/1.01  inst_lit_activity_moves:                0
% 1.48/1.01  inst_num_tautologies:                   0
% 1.48/1.01  inst_num_prop_implied:                  0
% 1.48/1.01  inst_num_existing_simplified:           0
% 1.48/1.01  inst_num_eq_res_simplified:             0
% 1.48/1.01  inst_num_child_elim:                    0
% 1.48/1.01  inst_num_of_dismatching_blockings:      39
% 1.48/1.01  inst_num_of_non_proper_insts:           150
% 1.48/1.01  inst_num_of_duplicates:                 0
% 1.48/1.01  inst_inst_num_from_inst_to_res:         0
% 1.48/1.01  inst_dismatching_checking_time:         0.
% 1.48/1.01  
% 1.48/1.01  ------ Resolution
% 1.48/1.01  
% 1.48/1.01  res_num_of_clauses:                     0
% 1.48/1.01  res_num_in_passive:                     0
% 1.48/1.01  res_num_in_active:                      0
% 1.48/1.01  res_num_of_loops:                       88
% 1.48/1.01  res_forward_subset_subsumed:            19
% 1.48/1.01  res_backward_subset_subsumed:           0
% 1.48/1.01  res_forward_subsumed:                   0
% 1.48/1.01  res_backward_subsumed:                  0
% 1.48/1.01  res_forward_subsumption_resolution:     0
% 1.48/1.01  res_backward_subsumption_resolution:    0
% 1.48/1.01  res_clause_to_clause_subsumption:       97
% 1.48/1.01  res_orphan_elimination:                 0
% 1.48/1.01  res_tautology_del:                      23
% 1.48/1.01  res_num_eq_res_simplified:              0
% 1.48/1.01  res_num_sel_changes:                    0
% 1.48/1.01  res_moves_from_active_to_pass:          0
% 1.48/1.01  
% 1.48/1.01  ------ Superposition
% 1.48/1.01  
% 1.48/1.01  sup_time_total:                         0.
% 1.48/1.01  sup_time_generating:                    0.
% 1.48/1.01  sup_time_sim_full:                      0.
% 1.48/1.01  sup_time_sim_immed:                     0.
% 1.48/1.01  
% 1.48/1.01  sup_num_of_clauses:                     41
% 1.48/1.01  sup_num_in_active:                      32
% 1.48/1.01  sup_num_in_passive:                     9
% 1.48/1.01  sup_num_of_loops:                       32
% 1.48/1.01  sup_fw_superposition:                   12
% 1.48/1.01  sup_bw_superposition:                   18
% 1.48/1.01  sup_immediate_simplified:               1
% 1.48/1.01  sup_given_eliminated:                   0
% 1.48/1.01  comparisons_done:                       0
% 1.48/1.01  comparisons_avoided:                    0
% 1.48/1.01  
% 1.48/1.01  ------ Simplifications
% 1.48/1.01  
% 1.48/1.01  
% 1.48/1.01  sim_fw_subset_subsumed:                 0
% 1.48/1.01  sim_bw_subset_subsumed:                 0
% 1.48/1.01  sim_fw_subsumed:                        1
% 1.48/1.01  sim_bw_subsumed:                        0
% 1.48/1.01  sim_fw_subsumption_res:                 1
% 1.48/1.01  sim_bw_subsumption_res:                 0
% 1.48/1.01  sim_tautology_del:                      1
% 1.48/1.01  sim_eq_tautology_del:                   0
% 1.48/1.01  sim_eq_res_simp:                        0
% 1.48/1.01  sim_fw_demodulated:                     0
% 1.48/1.01  sim_bw_demodulated:                     1
% 1.48/1.01  sim_light_normalised:                   0
% 1.48/1.01  sim_joinable_taut:                      0
% 1.48/1.01  sim_joinable_simp:                      0
% 1.48/1.01  sim_ac_normalised:                      0
% 1.48/1.01  sim_smt_subsumption:                    0
% 1.48/1.01  
%------------------------------------------------------------------------------
