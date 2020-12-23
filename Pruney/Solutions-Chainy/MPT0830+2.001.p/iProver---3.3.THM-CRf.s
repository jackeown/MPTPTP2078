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
% DateTime   : Thu Dec  3 11:55:25 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 267 expanded)
%              Number of clauses        :   65 ( 118 expanded)
%              Number of leaves         :   12 (  46 expanded)
%              Depth                    :   15
%              Number of atoms          :  252 ( 694 expanded)
%              Number of equality atoms :   68 ( 109 expanded)
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

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
   => ( ~ m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ~ m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f24,f31])).

fof(f47,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f48,plain,(
    ~ m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_767,plain,
    ( r2_hidden(sK0(X0_44,X1_44),X0_44)
    | r1_tarski(X0_44,X1_44) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1145,plain,
    ( r2_hidden(sK0(X0_44,X1_44),X0_44) = iProver_top
    | r1_tarski(X0_44,X1_44) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_767])).

cnf(c_9,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_762,plain,
    ( r1_tarski(k7_relat_1(X0_44,X1_44),X0_44)
    | ~ v1_relat_1(X0_44) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1150,plain,
    ( r1_tarski(k7_relat_1(X0_44,X1_44),X0_44) = iProver_top
    | v1_relat_1(X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_762])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_766,plain,
    ( ~ r2_hidden(X0_46,X0_44)
    | r2_hidden(X0_46,X1_44)
    | ~ r1_tarski(X0_44,X1_44) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1146,plain,
    ( r2_hidden(X0_46,X0_44) != iProver_top
    | r2_hidden(X0_46,X1_44) = iProver_top
    | r1_tarski(X0_44,X1_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_766])).

cnf(c_1472,plain,
    ( r2_hidden(X0_46,X0_44) = iProver_top
    | r2_hidden(X0_46,k7_relat_1(X0_44,X1_44)) != iProver_top
    | v1_relat_1(X0_44) != iProver_top ),
    inference(superposition,[status(thm)],[c_1150,c_1146])).

cnf(c_4233,plain,
    ( r2_hidden(sK0(k7_relat_1(X0_44,X1_44),X2_44),X0_44) = iProver_top
    | r1_tarski(k7_relat_1(X0_44,X1_44),X2_44) = iProver_top
    | v1_relat_1(X0_44) != iProver_top ),
    inference(superposition,[status(thm)],[c_1145,c_1472])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_757,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1155,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_757])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_764,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | r1_tarski(X0_44,X1_44) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1148,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(X1_44)) != iProver_top
    | r1_tarski(X0_44,X1_44) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_764])).

cnf(c_1336,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1155,c_1148])).

cnf(c_1471,plain,
    ( r2_hidden(X0_46,k2_zfmisc_1(sK1,sK3)) = iProver_top
    | r2_hidden(X0_46,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1336,c_1146])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_768,plain,
    ( ~ r2_hidden(sK0(X0_44,X1_44),X1_44)
    | r1_tarski(X0_44,X1_44) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1144,plain,
    ( r2_hidden(sK0(X0_44,X1_44),X1_44) != iProver_top
    | r1_tarski(X0_44,X1_44) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_768])).

cnf(c_1777,plain,
    ( r2_hidden(sK0(X0_44,k2_zfmisc_1(sK1,sK3)),sK4) != iProver_top
    | r1_tarski(X0_44,k2_zfmisc_1(sK1,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1471,c_1144])).

cnf(c_7244,plain,
    ( r1_tarski(k7_relat_1(sK4,X0_44),k2_zfmisc_1(sK1,sK3)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4233,c_1777])).

cnf(c_16,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_761,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X2_44)))
    | v1_relat_1(X0_44) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1249,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_761])).

cnf(c_1250,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1249])).

cnf(c_7716,plain,
    ( r1_tarski(k7_relat_1(sK4,X0_44),k2_zfmisc_1(sK1,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7244,c_16,c_1250])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_765,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(X1_44))
    | ~ r1_tarski(X0_44,X1_44) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1147,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(X1_44)) = iProver_top
    | r1_tarski(X0_44,X1_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_765])).

cnf(c_11,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_7,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_220,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_11,c_7])).

cnf(c_224,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_220,c_10])).

cnf(c_225,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_224])).

cnf(c_755,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X2_44)))
    | r1_tarski(k2_relat_1(X0_44),X2_44) ),
    inference(subtyping,[status(esa)],[c_225])).

cnf(c_1157,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X2_44))) != iProver_top
    | r1_tarski(k2_relat_1(X0_44),X2_44) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_755])).

cnf(c_2400,plain,
    ( r1_tarski(X0_44,k2_zfmisc_1(X1_44,X2_44)) != iProver_top
    | r1_tarski(k2_relat_1(X0_44),X2_44) = iProver_top ),
    inference(superposition,[status(thm)],[c_1147,c_1157])).

cnf(c_7725,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK4,X0_44)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_7716,c_2400])).

cnf(c_8,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_763,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_44,X1_44)),X1_44)
    | ~ v1_relat_1(X0_44) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1149,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0_44,X1_44)),X1_44) = iProver_top
    | v1_relat_1(X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_763])).

cnf(c_13,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_759,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X2_44)))
    | ~ r1_tarski(k1_relat_1(X0_44),X1_44)
    | ~ r1_tarski(k2_relat_1(X0_44),X2_44)
    | ~ v1_relat_1(X0_44) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1153,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X2_44))) = iProver_top
    | r1_tarski(k1_relat_1(X0_44),X1_44) != iProver_top
    | r1_tarski(k2_relat_1(X0_44),X2_44) != iProver_top
    | v1_relat_1(X0_44) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_759])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k5_relset_1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_760,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X2_44)))
    | k5_relset_1(X1_44,X2_44,X0_44,X3_44) = k7_relat_1(X0_44,X3_44) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1152,plain,
    ( k5_relset_1(X0_44,X1_44,X2_44,X3_44) = k7_relat_1(X2_44,X3_44)
    | m1_subset_1(X2_44,k1_zfmisc_1(k2_zfmisc_1(X0_44,X1_44))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_760])).

cnf(c_1604,plain,
    ( k5_relset_1(sK1,sK3,sK4,X0_44) = k7_relat_1(sK4,X0_44) ),
    inference(superposition,[status(thm)],[c_1155,c_1152])).

cnf(c_14,negated_conjecture,
    ( ~ m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_758,negated_conjecture,
    ( ~ m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1154,plain,
    ( m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_758])).

cnf(c_1675,plain,
    ( m1_subset_1(k7_relat_1(sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1604,c_1154])).

cnf(c_1930,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(sK4,sK2)),sK2) != iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK2)),sK3) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1153,c_1675])).

cnf(c_2272,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK4,sK2)),sK3) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK2)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1149,c_1930])).

cnf(c_2339,plain,
    ( v1_relat_1(k7_relat_1(sK4,sK2)) != iProver_top
    | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK2)),sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2272,c_16,c_1250])).

cnf(c_2340,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK4,sK2)),sK3) != iProver_top
    | v1_relat_1(k7_relat_1(sK4,sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2339])).

cnf(c_8175,plain,
    ( v1_relat_1(k7_relat_1(sK4,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7725,c_2340])).

cnf(c_1151,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X2_44))) != iProver_top
    | v1_relat_1(X0_44) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_761])).

cnf(c_1422,plain,
    ( r1_tarski(X0_44,k2_zfmisc_1(X1_44,X2_44)) != iProver_top
    | v1_relat_1(X0_44) = iProver_top ),
    inference(superposition,[status(thm)],[c_1147,c_1151])).

cnf(c_7726,plain,
    ( v1_relat_1(k7_relat_1(sK4,X0_44)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7716,c_1422])).

cnf(c_8495,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8175,c_7726])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : iproveropt_run.sh %d %s
% 0.11/0.30  % Computer   : n015.cluster.edu
% 0.11/0.30  % Model      : x86_64 x86_64
% 0.11/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.30  % Memory     : 8042.1875MB
% 0.11/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.30  % CPULimit   : 60
% 0.11/0.30  % WCLimit    : 600
% 0.11/0.30  % DateTime   : Tue Dec  1 14:08:23 EST 2020
% 0.11/0.30  % CPUTime    : 
% 0.11/0.30  % Running in FOF mode
% 2.60/0.95  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.60/0.95  
% 2.60/0.95  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.60/0.95  
% 2.60/0.95  ------  iProver source info
% 2.60/0.95  
% 2.60/0.95  git: date: 2020-06-30 10:37:57 +0100
% 2.60/0.95  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.60/0.95  git: non_committed_changes: false
% 2.60/0.95  git: last_make_outside_of_git: false
% 2.60/0.95  
% 2.60/0.95  ------ 
% 2.60/0.95  
% 2.60/0.95  ------ Input Options
% 2.60/0.95  
% 2.60/0.95  --out_options                           all
% 2.60/0.95  --tptp_safe_out                         true
% 2.60/0.95  --problem_path                          ""
% 2.60/0.95  --include_path                          ""
% 2.60/0.95  --clausifier                            res/vclausify_rel
% 2.60/0.95  --clausifier_options                    --mode clausify
% 2.60/0.95  --stdin                                 false
% 2.60/0.95  --stats_out                             all
% 2.60/0.95  
% 2.60/0.95  ------ General Options
% 2.60/0.95  
% 2.60/0.95  --fof                                   false
% 2.60/0.95  --time_out_real                         305.
% 2.60/0.95  --time_out_virtual                      -1.
% 2.60/0.95  --symbol_type_check                     false
% 2.60/0.95  --clausify_out                          false
% 2.60/0.95  --sig_cnt_out                           false
% 2.60/0.95  --trig_cnt_out                          false
% 2.60/0.95  --trig_cnt_out_tolerance                1.
% 2.60/0.95  --trig_cnt_out_sk_spl                   false
% 2.60/0.95  --abstr_cl_out                          false
% 2.60/0.95  
% 2.60/0.95  ------ Global Options
% 2.60/0.95  
% 2.60/0.95  --schedule                              default
% 2.60/0.95  --add_important_lit                     false
% 2.60/0.95  --prop_solver_per_cl                    1000
% 2.60/0.95  --min_unsat_core                        false
% 2.60/0.95  --soft_assumptions                      false
% 2.60/0.95  --soft_lemma_size                       3
% 2.60/0.95  --prop_impl_unit_size                   0
% 2.60/0.95  --prop_impl_unit                        []
% 2.60/0.95  --share_sel_clauses                     true
% 2.60/0.95  --reset_solvers                         false
% 2.60/0.95  --bc_imp_inh                            [conj_cone]
% 2.60/0.95  --conj_cone_tolerance                   3.
% 2.60/0.95  --extra_neg_conj                        none
% 2.60/0.95  --large_theory_mode                     true
% 2.60/0.95  --prolific_symb_bound                   200
% 2.60/0.95  --lt_threshold                          2000
% 2.60/0.95  --clause_weak_htbl                      true
% 2.60/0.95  --gc_record_bc_elim                     false
% 2.60/0.95  
% 2.60/0.95  ------ Preprocessing Options
% 2.60/0.95  
% 2.60/0.95  --preprocessing_flag                    true
% 2.60/0.95  --time_out_prep_mult                    0.1
% 2.60/0.95  --splitting_mode                        input
% 2.60/0.95  --splitting_grd                         true
% 2.60/0.95  --splitting_cvd                         false
% 2.60/0.95  --splitting_cvd_svl                     false
% 2.60/0.95  --splitting_nvd                         32
% 2.60/0.95  --sub_typing                            true
% 2.60/0.95  --prep_gs_sim                           true
% 2.60/0.95  --prep_unflatten                        true
% 2.60/0.95  --prep_res_sim                          true
% 2.60/0.95  --prep_upred                            true
% 2.60/0.95  --prep_sem_filter                       exhaustive
% 2.60/0.95  --prep_sem_filter_out                   false
% 2.60/0.95  --pred_elim                             true
% 2.60/0.95  --res_sim_input                         true
% 2.60/0.95  --eq_ax_congr_red                       true
% 2.60/0.95  --pure_diseq_elim                       true
% 2.60/0.95  --brand_transform                       false
% 2.60/0.95  --non_eq_to_eq                          false
% 2.60/0.95  --prep_def_merge                        true
% 2.60/0.95  --prep_def_merge_prop_impl              false
% 2.60/0.95  --prep_def_merge_mbd                    true
% 2.60/0.95  --prep_def_merge_tr_red                 false
% 2.60/0.95  --prep_def_merge_tr_cl                  false
% 2.60/0.95  --smt_preprocessing                     true
% 2.60/0.95  --smt_ac_axioms                         fast
% 2.60/0.95  --preprocessed_out                      false
% 2.60/0.95  --preprocessed_stats                    false
% 2.60/0.95  
% 2.60/0.95  ------ Abstraction refinement Options
% 2.60/0.95  
% 2.60/0.95  --abstr_ref                             []
% 2.60/0.95  --abstr_ref_prep                        false
% 2.60/0.95  --abstr_ref_until_sat                   false
% 2.60/0.95  --abstr_ref_sig_restrict                funpre
% 2.60/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 2.60/0.95  --abstr_ref_under                       []
% 2.60/0.95  
% 2.60/0.95  ------ SAT Options
% 2.60/0.95  
% 2.60/0.95  --sat_mode                              false
% 2.60/0.95  --sat_fm_restart_options                ""
% 2.60/0.95  --sat_gr_def                            false
% 2.60/0.95  --sat_epr_types                         true
% 2.60/0.95  --sat_non_cyclic_types                  false
% 2.60/0.95  --sat_finite_models                     false
% 2.60/0.95  --sat_fm_lemmas                         false
% 2.60/0.95  --sat_fm_prep                           false
% 2.60/0.95  --sat_fm_uc_incr                        true
% 2.60/0.95  --sat_out_model                         small
% 2.60/0.95  --sat_out_clauses                       false
% 2.60/0.95  
% 2.60/0.95  ------ QBF Options
% 2.60/0.95  
% 2.60/0.95  --qbf_mode                              false
% 2.60/0.95  --qbf_elim_univ                         false
% 2.60/0.95  --qbf_dom_inst                          none
% 2.60/0.95  --qbf_dom_pre_inst                      false
% 2.60/0.95  --qbf_sk_in                             false
% 2.60/0.95  --qbf_pred_elim                         true
% 2.60/0.95  --qbf_split                             512
% 2.60/0.95  
% 2.60/0.95  ------ BMC1 Options
% 2.60/0.95  
% 2.60/0.95  --bmc1_incremental                      false
% 2.60/0.95  --bmc1_axioms                           reachable_all
% 2.60/0.95  --bmc1_min_bound                        0
% 2.60/0.95  --bmc1_max_bound                        -1
% 2.60/0.95  --bmc1_max_bound_default                -1
% 2.60/0.95  --bmc1_symbol_reachability              true
% 2.60/0.95  --bmc1_property_lemmas                  false
% 2.60/0.95  --bmc1_k_induction                      false
% 2.60/0.95  --bmc1_non_equiv_states                 false
% 2.60/0.95  --bmc1_deadlock                         false
% 2.60/0.95  --bmc1_ucm                              false
% 2.60/0.95  --bmc1_add_unsat_core                   none
% 2.60/0.95  --bmc1_unsat_core_children              false
% 2.60/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 2.60/0.95  --bmc1_out_stat                         full
% 2.60/0.95  --bmc1_ground_init                      false
% 2.60/0.95  --bmc1_pre_inst_next_state              false
% 2.60/0.95  --bmc1_pre_inst_state                   false
% 2.60/0.95  --bmc1_pre_inst_reach_state             false
% 2.60/0.95  --bmc1_out_unsat_core                   false
% 2.60/0.95  --bmc1_aig_witness_out                  false
% 2.60/0.95  --bmc1_verbose                          false
% 2.60/0.95  --bmc1_dump_clauses_tptp                false
% 2.60/0.95  --bmc1_dump_unsat_core_tptp             false
% 2.60/0.95  --bmc1_dump_file                        -
% 2.60/0.95  --bmc1_ucm_expand_uc_limit              128
% 2.60/0.95  --bmc1_ucm_n_expand_iterations          6
% 2.60/0.95  --bmc1_ucm_extend_mode                  1
% 2.60/0.95  --bmc1_ucm_init_mode                    2
% 2.60/0.95  --bmc1_ucm_cone_mode                    none
% 2.60/0.95  --bmc1_ucm_reduced_relation_type        0
% 2.60/0.95  --bmc1_ucm_relax_model                  4
% 2.60/0.95  --bmc1_ucm_full_tr_after_sat            true
% 2.60/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 2.60/0.95  --bmc1_ucm_layered_model                none
% 2.60/0.95  --bmc1_ucm_max_lemma_size               10
% 2.60/0.95  
% 2.60/0.95  ------ AIG Options
% 2.60/0.95  
% 2.60/0.95  --aig_mode                              false
% 2.60/0.95  
% 2.60/0.95  ------ Instantiation Options
% 2.60/0.95  
% 2.60/0.95  --instantiation_flag                    true
% 2.60/0.95  --inst_sos_flag                         false
% 2.60/0.95  --inst_sos_phase                        true
% 2.60/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.60/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.60/0.95  --inst_lit_sel_side                     num_symb
% 2.60/0.95  --inst_solver_per_active                1400
% 2.60/0.95  --inst_solver_calls_frac                1.
% 2.60/0.95  --inst_passive_queue_type               priority_queues
% 2.60/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.60/0.95  --inst_passive_queues_freq              [25;2]
% 2.60/0.95  --inst_dismatching                      true
% 2.60/0.95  --inst_eager_unprocessed_to_passive     true
% 2.60/0.95  --inst_prop_sim_given                   true
% 2.60/0.95  --inst_prop_sim_new                     false
% 2.60/0.95  --inst_subs_new                         false
% 2.60/0.95  --inst_eq_res_simp                      false
% 2.60/0.95  --inst_subs_given                       false
% 2.60/0.95  --inst_orphan_elimination               true
% 2.60/0.95  --inst_learning_loop_flag               true
% 2.60/0.95  --inst_learning_start                   3000
% 2.60/0.95  --inst_learning_factor                  2
% 2.60/0.95  --inst_start_prop_sim_after_learn       3
% 2.60/0.95  --inst_sel_renew                        solver
% 2.60/0.95  --inst_lit_activity_flag                true
% 2.60/0.95  --inst_restr_to_given                   false
% 2.60/0.95  --inst_activity_threshold               500
% 2.60/0.95  --inst_out_proof                        true
% 2.60/0.95  
% 2.60/0.95  ------ Resolution Options
% 2.60/0.95  
% 2.60/0.95  --resolution_flag                       true
% 2.60/0.95  --res_lit_sel                           adaptive
% 2.60/0.95  --res_lit_sel_side                      none
% 2.60/0.95  --res_ordering                          kbo
% 2.60/0.95  --res_to_prop_solver                    active
% 2.60/0.95  --res_prop_simpl_new                    false
% 2.60/0.95  --res_prop_simpl_given                  true
% 2.60/0.95  --res_passive_queue_type                priority_queues
% 2.60/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.60/0.95  --res_passive_queues_freq               [15;5]
% 2.60/0.95  --res_forward_subs                      full
% 2.60/0.95  --res_backward_subs                     full
% 2.60/0.95  --res_forward_subs_resolution           true
% 2.60/0.95  --res_backward_subs_resolution          true
% 2.60/0.95  --res_orphan_elimination                true
% 2.60/0.95  --res_time_limit                        2.
% 2.60/0.95  --res_out_proof                         true
% 2.60/0.95  
% 2.60/0.95  ------ Superposition Options
% 2.60/0.95  
% 2.60/0.95  --superposition_flag                    true
% 2.60/0.95  --sup_passive_queue_type                priority_queues
% 2.60/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.60/0.95  --sup_passive_queues_freq               [8;1;4]
% 2.60/0.95  --demod_completeness_check              fast
% 2.60/0.95  --demod_use_ground                      true
% 2.60/0.95  --sup_to_prop_solver                    passive
% 2.60/0.95  --sup_prop_simpl_new                    true
% 2.60/0.95  --sup_prop_simpl_given                  true
% 2.60/0.95  --sup_fun_splitting                     false
% 2.60/0.95  --sup_smt_interval                      50000
% 2.60/0.95  
% 2.60/0.95  ------ Superposition Simplification Setup
% 2.60/0.95  
% 2.60/0.95  --sup_indices_passive                   []
% 2.60/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 2.60/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/0.95  --sup_full_bw                           [BwDemod]
% 2.60/0.95  --sup_immed_triv                        [TrivRules]
% 2.60/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.60/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/0.95  --sup_immed_bw_main                     []
% 2.60/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.60/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 2.60/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.60/0.95  
% 2.60/0.95  ------ Combination Options
% 2.60/0.95  
% 2.60/0.95  --comb_res_mult                         3
% 2.60/0.95  --comb_sup_mult                         2
% 2.60/0.95  --comb_inst_mult                        10
% 2.60/0.95  
% 2.60/0.95  ------ Debug Options
% 2.60/0.95  
% 2.60/0.95  --dbg_backtrace                         false
% 2.60/0.95  --dbg_dump_prop_clauses                 false
% 2.60/0.95  --dbg_dump_prop_clauses_file            -
% 2.60/0.95  --dbg_out_stat                          false
% 2.60/0.95  ------ Parsing...
% 2.60/0.95  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.60/0.95  
% 2.60/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.60/0.95  
% 2.60/0.95  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.60/0.95  
% 2.60/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.60/0.95  ------ Proving...
% 2.60/0.95  ------ Problem Properties 
% 2.60/0.95  
% 2.60/0.95  
% 2.60/0.95  clauses                                 14
% 2.60/0.95  conjectures                             2
% 2.60/0.95  EPR                                     2
% 2.60/0.95  Horn                                    13
% 2.60/0.95  unary                                   2
% 2.60/0.95  binary                                  9
% 2.60/0.95  lits                                    30
% 2.60/0.95  lits eq                                 1
% 2.60/0.95  fd_pure                                 0
% 2.60/0.95  fd_pseudo                               0
% 2.60/0.95  fd_cond                                 0
% 2.60/0.95  fd_pseudo_cond                          0
% 2.60/0.95  AC symbols                              0
% 2.60/0.95  
% 2.60/0.95  ------ Schedule dynamic 5 is on 
% 2.60/0.95  
% 2.60/0.95  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.60/0.95  
% 2.60/0.95  
% 2.60/0.95  ------ 
% 2.60/0.95  Current options:
% 2.60/0.95  ------ 
% 2.60/0.95  
% 2.60/0.95  ------ Input Options
% 2.60/0.95  
% 2.60/0.95  --out_options                           all
% 2.60/0.95  --tptp_safe_out                         true
% 2.60/0.95  --problem_path                          ""
% 2.60/0.95  --include_path                          ""
% 2.60/0.95  --clausifier                            res/vclausify_rel
% 2.60/0.95  --clausifier_options                    --mode clausify
% 2.60/0.95  --stdin                                 false
% 2.60/0.95  --stats_out                             all
% 2.60/0.95  
% 2.60/0.95  ------ General Options
% 2.60/0.95  
% 2.60/0.95  --fof                                   false
% 2.60/0.95  --time_out_real                         305.
% 2.60/0.95  --time_out_virtual                      -1.
% 2.60/0.95  --symbol_type_check                     false
% 2.60/0.95  --clausify_out                          false
% 2.60/0.95  --sig_cnt_out                           false
% 2.60/0.95  --trig_cnt_out                          false
% 2.60/0.95  --trig_cnt_out_tolerance                1.
% 2.60/0.95  --trig_cnt_out_sk_spl                   false
% 2.60/0.95  --abstr_cl_out                          false
% 2.60/0.95  
% 2.60/0.95  ------ Global Options
% 2.60/0.95  
% 2.60/0.95  --schedule                              default
% 2.60/0.95  --add_important_lit                     false
% 2.60/0.95  --prop_solver_per_cl                    1000
% 2.60/0.95  --min_unsat_core                        false
% 2.60/0.95  --soft_assumptions                      false
% 2.60/0.95  --soft_lemma_size                       3
% 2.60/0.95  --prop_impl_unit_size                   0
% 2.60/0.95  --prop_impl_unit                        []
% 2.60/0.95  --share_sel_clauses                     true
% 2.60/0.95  --reset_solvers                         false
% 2.60/0.95  --bc_imp_inh                            [conj_cone]
% 2.60/0.95  --conj_cone_tolerance                   3.
% 2.60/0.95  --extra_neg_conj                        none
% 2.60/0.95  --large_theory_mode                     true
% 2.60/0.95  --prolific_symb_bound                   200
% 2.60/0.95  --lt_threshold                          2000
% 2.60/0.95  --clause_weak_htbl                      true
% 2.60/0.95  --gc_record_bc_elim                     false
% 2.60/0.95  
% 2.60/0.95  ------ Preprocessing Options
% 2.60/0.95  
% 2.60/0.95  --preprocessing_flag                    true
% 2.60/0.95  --time_out_prep_mult                    0.1
% 2.60/0.95  --splitting_mode                        input
% 2.60/0.95  --splitting_grd                         true
% 2.60/0.95  --splitting_cvd                         false
% 2.60/0.95  --splitting_cvd_svl                     false
% 2.60/0.95  --splitting_nvd                         32
% 2.60/0.95  --sub_typing                            true
% 2.60/0.95  --prep_gs_sim                           true
% 2.60/0.95  --prep_unflatten                        true
% 2.60/0.95  --prep_res_sim                          true
% 2.60/0.95  --prep_upred                            true
% 2.60/0.95  --prep_sem_filter                       exhaustive
% 2.60/0.95  --prep_sem_filter_out                   false
% 2.60/0.95  --pred_elim                             true
% 2.60/0.95  --res_sim_input                         true
% 2.60/0.95  --eq_ax_congr_red                       true
% 2.60/0.95  --pure_diseq_elim                       true
% 2.60/0.95  --brand_transform                       false
% 2.60/0.95  --non_eq_to_eq                          false
% 2.60/0.95  --prep_def_merge                        true
% 2.60/0.95  --prep_def_merge_prop_impl              false
% 2.60/0.95  --prep_def_merge_mbd                    true
% 2.60/0.95  --prep_def_merge_tr_red                 false
% 2.60/0.95  --prep_def_merge_tr_cl                  false
% 2.60/0.95  --smt_preprocessing                     true
% 2.60/0.95  --smt_ac_axioms                         fast
% 2.60/0.95  --preprocessed_out                      false
% 2.60/0.95  --preprocessed_stats                    false
% 2.60/0.95  
% 2.60/0.95  ------ Abstraction refinement Options
% 2.60/0.95  
% 2.60/0.95  --abstr_ref                             []
% 2.60/0.95  --abstr_ref_prep                        false
% 2.60/0.95  --abstr_ref_until_sat                   false
% 2.60/0.95  --abstr_ref_sig_restrict                funpre
% 2.60/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 2.60/0.95  --abstr_ref_under                       []
% 2.60/0.95  
% 2.60/0.95  ------ SAT Options
% 2.60/0.95  
% 2.60/0.95  --sat_mode                              false
% 2.60/0.95  --sat_fm_restart_options                ""
% 2.60/0.95  --sat_gr_def                            false
% 2.60/0.95  --sat_epr_types                         true
% 2.60/0.95  --sat_non_cyclic_types                  false
% 2.60/0.95  --sat_finite_models                     false
% 2.60/0.95  --sat_fm_lemmas                         false
% 2.60/0.95  --sat_fm_prep                           false
% 2.60/0.95  --sat_fm_uc_incr                        true
% 2.60/0.95  --sat_out_model                         small
% 2.60/0.95  --sat_out_clauses                       false
% 2.60/0.95  
% 2.60/0.95  ------ QBF Options
% 2.60/0.95  
% 2.60/0.95  --qbf_mode                              false
% 2.60/0.95  --qbf_elim_univ                         false
% 2.60/0.95  --qbf_dom_inst                          none
% 2.60/0.95  --qbf_dom_pre_inst                      false
% 2.60/0.95  --qbf_sk_in                             false
% 2.60/0.95  --qbf_pred_elim                         true
% 2.60/0.95  --qbf_split                             512
% 2.60/0.95  
% 2.60/0.95  ------ BMC1 Options
% 2.60/0.95  
% 2.60/0.95  --bmc1_incremental                      false
% 2.60/0.95  --bmc1_axioms                           reachable_all
% 2.60/0.95  --bmc1_min_bound                        0
% 2.60/0.95  --bmc1_max_bound                        -1
% 2.60/0.95  --bmc1_max_bound_default                -1
% 2.60/0.95  --bmc1_symbol_reachability              true
% 2.60/0.95  --bmc1_property_lemmas                  false
% 2.60/0.95  --bmc1_k_induction                      false
% 2.60/0.95  --bmc1_non_equiv_states                 false
% 2.60/0.95  --bmc1_deadlock                         false
% 2.60/0.95  --bmc1_ucm                              false
% 2.60/0.95  --bmc1_add_unsat_core                   none
% 2.60/0.95  --bmc1_unsat_core_children              false
% 2.60/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 2.60/0.95  --bmc1_out_stat                         full
% 2.60/0.95  --bmc1_ground_init                      false
% 2.60/0.95  --bmc1_pre_inst_next_state              false
% 2.60/0.95  --bmc1_pre_inst_state                   false
% 2.60/0.95  --bmc1_pre_inst_reach_state             false
% 2.60/0.95  --bmc1_out_unsat_core                   false
% 2.60/0.95  --bmc1_aig_witness_out                  false
% 2.60/0.95  --bmc1_verbose                          false
% 2.60/0.95  --bmc1_dump_clauses_tptp                false
% 2.60/0.95  --bmc1_dump_unsat_core_tptp             false
% 2.60/0.95  --bmc1_dump_file                        -
% 2.60/0.95  --bmc1_ucm_expand_uc_limit              128
% 2.60/0.95  --bmc1_ucm_n_expand_iterations          6
% 2.60/0.95  --bmc1_ucm_extend_mode                  1
% 2.60/0.95  --bmc1_ucm_init_mode                    2
% 2.60/0.95  --bmc1_ucm_cone_mode                    none
% 2.60/0.95  --bmc1_ucm_reduced_relation_type        0
% 2.60/0.95  --bmc1_ucm_relax_model                  4
% 2.60/0.95  --bmc1_ucm_full_tr_after_sat            true
% 2.60/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 2.60/0.95  --bmc1_ucm_layered_model                none
% 2.60/0.95  --bmc1_ucm_max_lemma_size               10
% 2.60/0.95  
% 2.60/0.95  ------ AIG Options
% 2.60/0.95  
% 2.60/0.95  --aig_mode                              false
% 2.60/0.95  
% 2.60/0.95  ------ Instantiation Options
% 2.60/0.95  
% 2.60/0.95  --instantiation_flag                    true
% 2.60/0.95  --inst_sos_flag                         false
% 2.60/0.95  --inst_sos_phase                        true
% 2.60/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.60/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.60/0.95  --inst_lit_sel_side                     none
% 2.60/0.95  --inst_solver_per_active                1400
% 2.60/0.95  --inst_solver_calls_frac                1.
% 2.60/0.95  --inst_passive_queue_type               priority_queues
% 2.60/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.60/0.95  --inst_passive_queues_freq              [25;2]
% 2.60/0.95  --inst_dismatching                      true
% 2.60/0.95  --inst_eager_unprocessed_to_passive     true
% 2.60/0.95  --inst_prop_sim_given                   true
% 2.60/0.95  --inst_prop_sim_new                     false
% 2.60/0.95  --inst_subs_new                         false
% 2.60/0.95  --inst_eq_res_simp                      false
% 2.60/0.95  --inst_subs_given                       false
% 2.60/0.95  --inst_orphan_elimination               true
% 2.60/0.95  --inst_learning_loop_flag               true
% 2.60/0.95  --inst_learning_start                   3000
% 2.60/0.95  --inst_learning_factor                  2
% 2.60/0.95  --inst_start_prop_sim_after_learn       3
% 2.60/0.95  --inst_sel_renew                        solver
% 2.60/0.95  --inst_lit_activity_flag                true
% 2.60/0.95  --inst_restr_to_given                   false
% 2.60/0.95  --inst_activity_threshold               500
% 2.60/0.95  --inst_out_proof                        true
% 2.60/0.95  
% 2.60/0.95  ------ Resolution Options
% 2.60/0.95  
% 2.60/0.95  --resolution_flag                       false
% 2.60/0.95  --res_lit_sel                           adaptive
% 2.60/0.95  --res_lit_sel_side                      none
% 2.60/0.95  --res_ordering                          kbo
% 2.60/0.95  --res_to_prop_solver                    active
% 2.60/0.95  --res_prop_simpl_new                    false
% 2.60/0.95  --res_prop_simpl_given                  true
% 2.60/0.95  --res_passive_queue_type                priority_queues
% 2.60/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.60/0.95  --res_passive_queues_freq               [15;5]
% 2.60/0.95  --res_forward_subs                      full
% 2.60/0.95  --res_backward_subs                     full
% 2.60/0.95  --res_forward_subs_resolution           true
% 2.60/0.95  --res_backward_subs_resolution          true
% 2.60/0.95  --res_orphan_elimination                true
% 2.60/0.95  --res_time_limit                        2.
% 2.60/0.95  --res_out_proof                         true
% 2.60/0.95  
% 2.60/0.95  ------ Superposition Options
% 2.60/0.95  
% 2.60/0.95  --superposition_flag                    true
% 2.60/0.95  --sup_passive_queue_type                priority_queues
% 2.60/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.60/0.95  --sup_passive_queues_freq               [8;1;4]
% 2.60/0.95  --demod_completeness_check              fast
% 2.60/0.96  --demod_use_ground                      true
% 2.60/0.96  --sup_to_prop_solver                    passive
% 2.60/0.96  --sup_prop_simpl_new                    true
% 2.60/0.96  --sup_prop_simpl_given                  true
% 2.60/0.96  --sup_fun_splitting                     false
% 2.60/0.96  --sup_smt_interval                      50000
% 2.60/0.96  
% 2.60/0.96  ------ Superposition Simplification Setup
% 2.60/0.96  
% 2.60/0.96  --sup_indices_passive                   []
% 2.60/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.60/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 2.60/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/0.96  --sup_full_bw                           [BwDemod]
% 2.60/0.96  --sup_immed_triv                        [TrivRules]
% 2.60/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.60/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/0.96  --sup_immed_bw_main                     []
% 2.60/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.60/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 2.60/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.60/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.60/0.96  
% 2.60/0.96  ------ Combination Options
% 2.60/0.96  
% 2.60/0.96  --comb_res_mult                         3
% 2.60/0.96  --comb_sup_mult                         2
% 2.60/0.96  --comb_inst_mult                        10
% 2.60/0.96  
% 2.60/0.96  ------ Debug Options
% 2.60/0.96  
% 2.60/0.96  --dbg_backtrace                         false
% 2.60/0.96  --dbg_dump_prop_clauses                 false
% 2.60/0.96  --dbg_dump_prop_clauses_file            -
% 2.60/0.96  --dbg_out_stat                          false
% 2.60/0.96  
% 2.60/0.96  
% 2.60/0.96  
% 2.60/0.96  
% 2.60/0.96  ------ Proving...
% 2.60/0.96  
% 2.60/0.96  
% 2.60/0.96  % SZS status Theorem for theBenchmark.p
% 2.60/0.96  
% 2.60/0.96   Resolution empty clause
% 2.60/0.96  
% 2.60/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 2.60/0.96  
% 2.60/0.96  fof(f1,axiom,(
% 2.60/0.96    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.60/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.60/0.96  
% 2.60/0.96  fof(f14,plain,(
% 2.60/0.96    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.60/0.96    inference(ennf_transformation,[],[f1])).
% 2.60/0.96  
% 2.60/0.96  fof(f25,plain,(
% 2.60/0.96    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.60/0.96    inference(nnf_transformation,[],[f14])).
% 2.60/0.96  
% 2.60/0.96  fof(f26,plain,(
% 2.60/0.96    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.60/0.96    inference(rectify,[],[f25])).
% 2.60/0.96  
% 2.60/0.96  fof(f27,plain,(
% 2.60/0.96    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.60/0.96    introduced(choice_axiom,[])).
% 2.60/0.96  
% 2.60/0.96  fof(f28,plain,(
% 2.60/0.96    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.60/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 2.60/0.96  
% 2.60/0.96  fof(f34,plain,(
% 2.60/0.96    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.60/0.96    inference(cnf_transformation,[],[f28])).
% 2.60/0.96  
% 2.60/0.96  fof(f6,axiom,(
% 2.60/0.96    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 2.60/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.60/0.96  
% 2.60/0.96  fof(f18,plain,(
% 2.60/0.96    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 2.60/0.96    inference(ennf_transformation,[],[f6])).
% 2.60/0.96  
% 2.60/0.96  fof(f42,plain,(
% 2.60/0.96    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 2.60/0.96    inference(cnf_transformation,[],[f18])).
% 2.60/0.96  
% 2.60/0.96  fof(f33,plain,(
% 2.60/0.96    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.60/0.96    inference(cnf_transformation,[],[f28])).
% 2.60/0.96  
% 2.60/0.96  fof(f11,conjecture,(
% 2.60/0.96    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 2.60/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.60/0.96  
% 2.60/0.96  fof(f12,negated_conjecture,(
% 2.60/0.96    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 2.60/0.96    inference(negated_conjecture,[],[f11])).
% 2.60/0.96  
% 2.60/0.96  fof(f24,plain,(
% 2.60/0.96    ? [X0,X1,X2,X3] : (~m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 2.60/0.96    inference(ennf_transformation,[],[f12])).
% 2.60/0.96  
% 2.60/0.96  fof(f31,plain,(
% 2.60/0.96    ? [X0,X1,X2,X3] : (~m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) => (~m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))))),
% 2.60/0.96    introduced(choice_axiom,[])).
% 2.60/0.96  
% 2.60/0.96  fof(f32,plain,(
% 2.60/0.96    ~m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 2.60/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f24,f31])).
% 2.60/0.96  
% 2.60/0.96  fof(f47,plain,(
% 2.60/0.96    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))),
% 2.60/0.96    inference(cnf_transformation,[],[f32])).
% 2.60/0.96  
% 2.60/0.96  fof(f2,axiom,(
% 2.60/0.96    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.60/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.60/0.96  
% 2.60/0.96  fof(f29,plain,(
% 2.60/0.96    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.60/0.96    inference(nnf_transformation,[],[f2])).
% 2.60/0.96  
% 2.60/0.96  fof(f36,plain,(
% 2.60/0.96    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.60/0.96    inference(cnf_transformation,[],[f29])).
% 2.60/0.96  
% 2.60/0.96  fof(f35,plain,(
% 2.60/0.96    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.60/0.96    inference(cnf_transformation,[],[f28])).
% 2.60/0.96  
% 2.60/0.96  fof(f7,axiom,(
% 2.60/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.60/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.60/0.96  
% 2.60/0.96  fof(f19,plain,(
% 2.60/0.96    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.60/0.96    inference(ennf_transformation,[],[f7])).
% 2.60/0.96  
% 2.60/0.96  fof(f43,plain,(
% 2.60/0.96    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.60/0.96    inference(cnf_transformation,[],[f19])).
% 2.60/0.96  
% 2.60/0.96  fof(f37,plain,(
% 2.60/0.96    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.60/0.96    inference(cnf_transformation,[],[f29])).
% 2.60/0.96  
% 2.60/0.96  fof(f8,axiom,(
% 2.60/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.60/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.60/0.96  
% 2.60/0.96  fof(f13,plain,(
% 2.60/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.60/0.96    inference(pure_predicate_removal,[],[f8])).
% 2.60/0.96  
% 2.60/0.96  fof(f20,plain,(
% 2.60/0.96    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.60/0.96    inference(ennf_transformation,[],[f13])).
% 2.60/0.96  
% 2.60/0.96  fof(f44,plain,(
% 2.60/0.96    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.60/0.96    inference(cnf_transformation,[],[f20])).
% 2.60/0.96  
% 2.60/0.96  fof(f4,axiom,(
% 2.60/0.96    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.60/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.60/0.96  
% 2.60/0.96  fof(f16,plain,(
% 2.60/0.96    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.60/0.96    inference(ennf_transformation,[],[f4])).
% 2.60/0.96  
% 2.60/0.96  fof(f30,plain,(
% 2.60/0.96    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.60/0.96    inference(nnf_transformation,[],[f16])).
% 2.60/0.96  
% 2.60/0.96  fof(f39,plain,(
% 2.60/0.96    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.60/0.96    inference(cnf_transformation,[],[f30])).
% 2.60/0.96  
% 2.60/0.96  fof(f5,axiom,(
% 2.60/0.96    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 2.60/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.60/0.96  
% 2.60/0.96  fof(f17,plain,(
% 2.60/0.96    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 2.60/0.96    inference(ennf_transformation,[],[f5])).
% 2.60/0.96  
% 2.60/0.96  fof(f41,plain,(
% 2.60/0.96    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 2.60/0.96    inference(cnf_transformation,[],[f17])).
% 2.60/0.96  
% 2.60/0.96  fof(f10,axiom,(
% 2.60/0.96    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.60/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.60/0.96  
% 2.60/0.96  fof(f22,plain,(
% 2.60/0.96    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 2.60/0.96    inference(ennf_transformation,[],[f10])).
% 2.60/0.96  
% 2.60/0.96  fof(f23,plain,(
% 2.60/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 2.60/0.96    inference(flattening,[],[f22])).
% 2.60/0.96  
% 2.60/0.96  fof(f46,plain,(
% 2.60/0.96    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 2.60/0.96    inference(cnf_transformation,[],[f23])).
% 2.60/0.96  
% 2.60/0.96  fof(f9,axiom,(
% 2.60/0.96    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3))),
% 2.60/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.60/0.96  
% 2.60/0.96  fof(f21,plain,(
% 2.60/0.96    ! [X0,X1,X2,X3] : (k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.60/0.96    inference(ennf_transformation,[],[f9])).
% 2.60/0.96  
% 2.60/0.96  fof(f45,plain,(
% 2.60/0.96    ( ! [X2,X0,X3,X1] : (k7_relat_1(X2,X3) = k5_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.60/0.96    inference(cnf_transformation,[],[f21])).
% 2.60/0.96  
% 2.60/0.96  fof(f48,plain,(
% 2.60/0.96    ~m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.60/0.96    inference(cnf_transformation,[],[f32])).
% 2.60/0.96  
% 2.60/0.96  cnf(c_1,plain,
% 2.60/0.96      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.60/0.96      inference(cnf_transformation,[],[f34]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_767,plain,
% 2.60/0.96      ( r2_hidden(sK0(X0_44,X1_44),X0_44) | r1_tarski(X0_44,X1_44) ),
% 2.60/0.96      inference(subtyping,[status(esa)],[c_1]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_1145,plain,
% 2.60/0.96      ( r2_hidden(sK0(X0_44,X1_44),X0_44) = iProver_top
% 2.60/0.96      | r1_tarski(X0_44,X1_44) = iProver_top ),
% 2.60/0.96      inference(predicate_to_equality,[status(thm)],[c_767]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_9,plain,
% 2.60/0.96      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 2.60/0.96      inference(cnf_transformation,[],[f42]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_762,plain,
% 2.60/0.96      ( r1_tarski(k7_relat_1(X0_44,X1_44),X0_44) | ~ v1_relat_1(X0_44) ),
% 2.60/0.96      inference(subtyping,[status(esa)],[c_9]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_1150,plain,
% 2.60/0.96      ( r1_tarski(k7_relat_1(X0_44,X1_44),X0_44) = iProver_top
% 2.60/0.96      | v1_relat_1(X0_44) != iProver_top ),
% 2.60/0.96      inference(predicate_to_equality,[status(thm)],[c_762]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_2,plain,
% 2.60/0.96      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 2.60/0.96      inference(cnf_transformation,[],[f33]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_766,plain,
% 2.60/0.96      ( ~ r2_hidden(X0_46,X0_44)
% 2.60/0.96      | r2_hidden(X0_46,X1_44)
% 2.60/0.96      | ~ r1_tarski(X0_44,X1_44) ),
% 2.60/0.96      inference(subtyping,[status(esa)],[c_2]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_1146,plain,
% 2.60/0.96      ( r2_hidden(X0_46,X0_44) != iProver_top
% 2.60/0.96      | r2_hidden(X0_46,X1_44) = iProver_top
% 2.60/0.96      | r1_tarski(X0_44,X1_44) != iProver_top ),
% 2.60/0.96      inference(predicate_to_equality,[status(thm)],[c_766]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_1472,plain,
% 2.60/0.96      ( r2_hidden(X0_46,X0_44) = iProver_top
% 2.60/0.96      | r2_hidden(X0_46,k7_relat_1(X0_44,X1_44)) != iProver_top
% 2.60/0.96      | v1_relat_1(X0_44) != iProver_top ),
% 2.60/0.96      inference(superposition,[status(thm)],[c_1150,c_1146]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_4233,plain,
% 2.60/0.96      ( r2_hidden(sK0(k7_relat_1(X0_44,X1_44),X2_44),X0_44) = iProver_top
% 2.60/0.96      | r1_tarski(k7_relat_1(X0_44,X1_44),X2_44) = iProver_top
% 2.60/0.96      | v1_relat_1(X0_44) != iProver_top ),
% 2.60/0.96      inference(superposition,[status(thm)],[c_1145,c_1472]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_15,negated_conjecture,
% 2.60/0.96      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
% 2.60/0.96      inference(cnf_transformation,[],[f47]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_757,negated_conjecture,
% 2.60/0.96      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) ),
% 2.60/0.96      inference(subtyping,[status(esa)],[c_15]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_1155,plain,
% 2.60/0.96      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top ),
% 2.60/0.96      inference(predicate_to_equality,[status(thm)],[c_757]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_4,plain,
% 2.60/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.60/0.96      inference(cnf_transformation,[],[f36]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_764,plain,
% 2.60/0.96      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X1_44)) | r1_tarski(X0_44,X1_44) ),
% 2.60/0.96      inference(subtyping,[status(esa)],[c_4]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_1148,plain,
% 2.60/0.96      ( m1_subset_1(X0_44,k1_zfmisc_1(X1_44)) != iProver_top
% 2.60/0.96      | r1_tarski(X0_44,X1_44) = iProver_top ),
% 2.60/0.96      inference(predicate_to_equality,[status(thm)],[c_764]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_1336,plain,
% 2.60/0.96      ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK3)) = iProver_top ),
% 2.60/0.96      inference(superposition,[status(thm)],[c_1155,c_1148]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_1471,plain,
% 2.60/0.96      ( r2_hidden(X0_46,k2_zfmisc_1(sK1,sK3)) = iProver_top
% 2.60/0.96      | r2_hidden(X0_46,sK4) != iProver_top ),
% 2.60/0.96      inference(superposition,[status(thm)],[c_1336,c_1146]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_0,plain,
% 2.60/0.96      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.60/0.96      inference(cnf_transformation,[],[f35]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_768,plain,
% 2.60/0.96      ( ~ r2_hidden(sK0(X0_44,X1_44),X1_44) | r1_tarski(X0_44,X1_44) ),
% 2.60/0.96      inference(subtyping,[status(esa)],[c_0]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_1144,plain,
% 2.60/0.96      ( r2_hidden(sK0(X0_44,X1_44),X1_44) != iProver_top
% 2.60/0.96      | r1_tarski(X0_44,X1_44) = iProver_top ),
% 2.60/0.96      inference(predicate_to_equality,[status(thm)],[c_768]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_1777,plain,
% 2.60/0.96      ( r2_hidden(sK0(X0_44,k2_zfmisc_1(sK1,sK3)),sK4) != iProver_top
% 2.60/0.96      | r1_tarski(X0_44,k2_zfmisc_1(sK1,sK3)) = iProver_top ),
% 2.60/0.96      inference(superposition,[status(thm)],[c_1471,c_1144]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_7244,plain,
% 2.60/0.96      ( r1_tarski(k7_relat_1(sK4,X0_44),k2_zfmisc_1(sK1,sK3)) = iProver_top
% 2.60/0.96      | v1_relat_1(sK4) != iProver_top ),
% 2.60/0.96      inference(superposition,[status(thm)],[c_4233,c_1777]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_16,plain,
% 2.60/0.96      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) = iProver_top ),
% 2.60/0.96      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_10,plain,
% 2.60/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.60/0.96      inference(cnf_transformation,[],[f43]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_761,plain,
% 2.60/0.96      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X2_44)))
% 2.60/0.96      | v1_relat_1(X0_44) ),
% 2.60/0.96      inference(subtyping,[status(esa)],[c_10]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_1249,plain,
% 2.60/0.96      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3)))
% 2.60/0.96      | v1_relat_1(sK4) ),
% 2.60/0.96      inference(instantiation,[status(thm)],[c_761]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_1250,plain,
% 2.60/0.96      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK3))) != iProver_top
% 2.60/0.96      | v1_relat_1(sK4) = iProver_top ),
% 2.60/0.96      inference(predicate_to_equality,[status(thm)],[c_1249]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_7716,plain,
% 2.60/0.96      ( r1_tarski(k7_relat_1(sK4,X0_44),k2_zfmisc_1(sK1,sK3)) = iProver_top ),
% 2.60/0.96      inference(global_propositional_subsumption,
% 2.60/0.96                [status(thm)],
% 2.60/0.96                [c_7244,c_16,c_1250]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_3,plain,
% 2.60/0.96      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.60/0.96      inference(cnf_transformation,[],[f37]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_765,plain,
% 2.60/0.96      ( m1_subset_1(X0_44,k1_zfmisc_1(X1_44)) | ~ r1_tarski(X0_44,X1_44) ),
% 2.60/0.96      inference(subtyping,[status(esa)],[c_3]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_1147,plain,
% 2.60/0.96      ( m1_subset_1(X0_44,k1_zfmisc_1(X1_44)) = iProver_top
% 2.60/0.96      | r1_tarski(X0_44,X1_44) != iProver_top ),
% 2.60/0.96      inference(predicate_to_equality,[status(thm)],[c_765]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_11,plain,
% 2.60/0.96      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.60/0.96      inference(cnf_transformation,[],[f44]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_7,plain,
% 2.60/0.96      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 2.60/0.96      inference(cnf_transformation,[],[f39]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_220,plain,
% 2.60/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.60/0.96      | r1_tarski(k2_relat_1(X0),X2)
% 2.60/0.96      | ~ v1_relat_1(X0) ),
% 2.60/0.96      inference(resolution,[status(thm)],[c_11,c_7]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_224,plain,
% 2.60/0.96      ( r1_tarski(k2_relat_1(X0),X2)
% 2.60/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.60/0.96      inference(global_propositional_subsumption,[status(thm)],[c_220,c_10]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_225,plain,
% 2.60/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.60/0.96      | r1_tarski(k2_relat_1(X0),X2) ),
% 2.60/0.96      inference(renaming,[status(thm)],[c_224]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_755,plain,
% 2.60/0.96      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X2_44)))
% 2.60/0.96      | r1_tarski(k2_relat_1(X0_44),X2_44) ),
% 2.60/0.96      inference(subtyping,[status(esa)],[c_225]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_1157,plain,
% 2.60/0.96      ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X2_44))) != iProver_top
% 2.60/0.96      | r1_tarski(k2_relat_1(X0_44),X2_44) = iProver_top ),
% 2.60/0.96      inference(predicate_to_equality,[status(thm)],[c_755]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_2400,plain,
% 2.60/0.96      ( r1_tarski(X0_44,k2_zfmisc_1(X1_44,X2_44)) != iProver_top
% 2.60/0.96      | r1_tarski(k2_relat_1(X0_44),X2_44) = iProver_top ),
% 2.60/0.96      inference(superposition,[status(thm)],[c_1147,c_1157]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_7725,plain,
% 2.60/0.96      ( r1_tarski(k2_relat_1(k7_relat_1(sK4,X0_44)),sK3) = iProver_top ),
% 2.60/0.96      inference(superposition,[status(thm)],[c_7716,c_2400]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_8,plain,
% 2.60/0.96      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 2.60/0.96      inference(cnf_transformation,[],[f41]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_763,plain,
% 2.60/0.96      ( r1_tarski(k1_relat_1(k7_relat_1(X0_44,X1_44)),X1_44)
% 2.60/0.96      | ~ v1_relat_1(X0_44) ),
% 2.60/0.96      inference(subtyping,[status(esa)],[c_8]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_1149,plain,
% 2.60/0.96      ( r1_tarski(k1_relat_1(k7_relat_1(X0_44,X1_44)),X1_44) = iProver_top
% 2.60/0.96      | v1_relat_1(X0_44) != iProver_top ),
% 2.60/0.96      inference(predicate_to_equality,[status(thm)],[c_763]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_13,plain,
% 2.60/0.96      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.60/0.96      | ~ r1_tarski(k1_relat_1(X0),X1)
% 2.60/0.96      | ~ r1_tarski(k2_relat_1(X0),X2)
% 2.60/0.96      | ~ v1_relat_1(X0) ),
% 2.60/0.96      inference(cnf_transformation,[],[f46]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_759,plain,
% 2.60/0.96      ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X2_44)))
% 2.60/0.96      | ~ r1_tarski(k1_relat_1(X0_44),X1_44)
% 2.60/0.96      | ~ r1_tarski(k2_relat_1(X0_44),X2_44)
% 2.60/0.96      | ~ v1_relat_1(X0_44) ),
% 2.60/0.96      inference(subtyping,[status(esa)],[c_13]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_1153,plain,
% 2.60/0.96      ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X2_44))) = iProver_top
% 2.60/0.96      | r1_tarski(k1_relat_1(X0_44),X1_44) != iProver_top
% 2.60/0.96      | r1_tarski(k2_relat_1(X0_44),X2_44) != iProver_top
% 2.60/0.96      | v1_relat_1(X0_44) != iProver_top ),
% 2.60/0.96      inference(predicate_to_equality,[status(thm)],[c_759]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_12,plain,
% 2.60/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.60/0.96      | k5_relset_1(X1,X2,X0,X3) = k7_relat_1(X0,X3) ),
% 2.60/0.96      inference(cnf_transformation,[],[f45]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_760,plain,
% 2.60/0.96      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X2_44)))
% 2.60/0.96      | k5_relset_1(X1_44,X2_44,X0_44,X3_44) = k7_relat_1(X0_44,X3_44) ),
% 2.60/0.96      inference(subtyping,[status(esa)],[c_12]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_1152,plain,
% 2.60/0.96      ( k5_relset_1(X0_44,X1_44,X2_44,X3_44) = k7_relat_1(X2_44,X3_44)
% 2.60/0.96      | m1_subset_1(X2_44,k1_zfmisc_1(k2_zfmisc_1(X0_44,X1_44))) != iProver_top ),
% 2.60/0.96      inference(predicate_to_equality,[status(thm)],[c_760]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_1604,plain,
% 2.60/0.96      ( k5_relset_1(sK1,sK3,sK4,X0_44) = k7_relat_1(sK4,X0_44) ),
% 2.60/0.96      inference(superposition,[status(thm)],[c_1155,c_1152]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_14,negated_conjecture,
% 2.60/0.96      ( ~ m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.60/0.96      inference(cnf_transformation,[],[f48]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_758,negated_conjecture,
% 2.60/0.96      ( ~ m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.60/0.96      inference(subtyping,[status(esa)],[c_14]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_1154,plain,
% 2.60/0.96      ( m1_subset_1(k5_relset_1(sK1,sK3,sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 2.60/0.96      inference(predicate_to_equality,[status(thm)],[c_758]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_1675,plain,
% 2.60/0.96      ( m1_subset_1(k7_relat_1(sK4,sK2),k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 2.60/0.96      inference(demodulation,[status(thm)],[c_1604,c_1154]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_1930,plain,
% 2.60/0.96      ( r1_tarski(k1_relat_1(k7_relat_1(sK4,sK2)),sK2) != iProver_top
% 2.60/0.96      | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK2)),sK3) != iProver_top
% 2.60/0.96      | v1_relat_1(k7_relat_1(sK4,sK2)) != iProver_top ),
% 2.60/0.96      inference(superposition,[status(thm)],[c_1153,c_1675]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_2272,plain,
% 2.60/0.96      ( r1_tarski(k2_relat_1(k7_relat_1(sK4,sK2)),sK3) != iProver_top
% 2.60/0.96      | v1_relat_1(k7_relat_1(sK4,sK2)) != iProver_top
% 2.60/0.96      | v1_relat_1(sK4) != iProver_top ),
% 2.60/0.96      inference(superposition,[status(thm)],[c_1149,c_1930]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_2339,plain,
% 2.60/0.96      ( v1_relat_1(k7_relat_1(sK4,sK2)) != iProver_top
% 2.60/0.96      | r1_tarski(k2_relat_1(k7_relat_1(sK4,sK2)),sK3) != iProver_top ),
% 2.60/0.96      inference(global_propositional_subsumption,
% 2.60/0.96                [status(thm)],
% 2.60/0.96                [c_2272,c_16,c_1250]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_2340,plain,
% 2.60/0.96      ( r1_tarski(k2_relat_1(k7_relat_1(sK4,sK2)),sK3) != iProver_top
% 2.60/0.96      | v1_relat_1(k7_relat_1(sK4,sK2)) != iProver_top ),
% 2.60/0.96      inference(renaming,[status(thm)],[c_2339]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_8175,plain,
% 2.60/0.96      ( v1_relat_1(k7_relat_1(sK4,sK2)) != iProver_top ),
% 2.60/0.96      inference(superposition,[status(thm)],[c_7725,c_2340]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_1151,plain,
% 2.60/0.96      ( m1_subset_1(X0_44,k1_zfmisc_1(k2_zfmisc_1(X1_44,X2_44))) != iProver_top
% 2.60/0.96      | v1_relat_1(X0_44) = iProver_top ),
% 2.60/0.96      inference(predicate_to_equality,[status(thm)],[c_761]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_1422,plain,
% 2.60/0.96      ( r1_tarski(X0_44,k2_zfmisc_1(X1_44,X2_44)) != iProver_top
% 2.60/0.96      | v1_relat_1(X0_44) = iProver_top ),
% 2.60/0.96      inference(superposition,[status(thm)],[c_1147,c_1151]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_7726,plain,
% 2.60/0.96      ( v1_relat_1(k7_relat_1(sK4,X0_44)) = iProver_top ),
% 2.60/0.96      inference(superposition,[status(thm)],[c_7716,c_1422]) ).
% 2.60/0.96  
% 2.60/0.96  cnf(c_8495,plain,
% 2.60/0.96      ( $false ),
% 2.60/0.96      inference(forward_subsumption_resolution,[status(thm)],[c_8175,c_7726]) ).
% 2.60/0.96  
% 2.60/0.96  
% 2.60/0.96  % SZS output end CNFRefutation for theBenchmark.p
% 2.60/0.96  
% 2.60/0.96  ------                               Statistics
% 2.60/0.96  
% 2.60/0.96  ------ General
% 2.60/0.96  
% 2.60/0.96  abstr_ref_over_cycles:                  0
% 2.60/0.96  abstr_ref_under_cycles:                 0
% 2.60/0.96  gc_basic_clause_elim:                   0
% 2.60/0.96  forced_gc_time:                         0
% 2.60/0.96  parsing_time:                           0.01
% 2.60/0.96  unif_index_cands_time:                  0.
% 2.60/0.96  unif_index_add_time:                    0.
% 2.60/0.96  orderings_time:                         0.
% 2.60/0.96  out_proof_time:                         0.007
% 2.60/0.96  total_time:                             0.245
% 2.60/0.96  num_of_symbols:                         50
% 2.60/0.96  num_of_terms:                           9973
% 2.60/0.96  
% 2.60/0.96  ------ Preprocessing
% 2.60/0.96  
% 2.60/0.96  num_of_splits:                          0
% 2.60/0.96  num_of_split_atoms:                     0
% 2.60/0.96  num_of_reused_defs:                     0
% 2.60/0.96  num_eq_ax_congr_red:                    26
% 2.60/0.96  num_of_sem_filtered_clauses:            1
% 2.60/0.96  num_of_subtypes:                        3
% 2.60/0.96  monotx_restored_types:                  0
% 2.60/0.96  sat_num_of_epr_types:                   0
% 2.60/0.96  sat_num_of_non_cyclic_types:            0
% 2.60/0.96  sat_guarded_non_collapsed_types:        0
% 2.60/0.96  num_pure_diseq_elim:                    0
% 2.60/0.96  simp_replaced_by:                       0
% 2.60/0.96  res_preprocessed:                       81
% 2.60/0.96  prep_upred:                             0
% 2.60/0.96  prep_unflattend:                        20
% 2.60/0.96  smt_new_axioms:                         0
% 2.60/0.96  pred_elim_cands:                        4
% 2.60/0.96  pred_elim:                              1
% 2.60/0.96  pred_elim_cl:                           2
% 2.60/0.96  pred_elim_cycles:                       3
% 2.60/0.96  merged_defs:                            8
% 2.60/0.96  merged_defs_ncl:                        0
% 2.60/0.96  bin_hyper_res:                          9
% 2.60/0.96  prep_cycles:                            4
% 2.60/0.96  pred_elim_time:                         0.007
% 2.60/0.96  splitting_time:                         0.
% 2.60/0.96  sem_filter_time:                        0.
% 2.60/0.96  monotx_time:                            0.
% 2.60/0.96  subtype_inf_time:                       0.
% 2.60/0.96  
% 2.60/0.96  ------ Problem properties
% 2.60/0.96  
% 2.60/0.96  clauses:                                14
% 2.60/0.96  conjectures:                            2
% 2.60/0.96  epr:                                    2
% 2.60/0.96  horn:                                   13
% 2.60/0.96  ground:                                 2
% 2.60/0.96  unary:                                  2
% 2.60/0.96  binary:                                 9
% 2.60/0.96  lits:                                   30
% 2.60/0.96  lits_eq:                                1
% 2.60/0.96  fd_pure:                                0
% 2.60/0.96  fd_pseudo:                              0
% 2.60/0.96  fd_cond:                                0
% 2.60/0.96  fd_pseudo_cond:                         0
% 2.60/0.96  ac_symbols:                             0
% 2.60/0.96  
% 2.60/0.96  ------ Propositional Solver
% 2.60/0.96  
% 2.60/0.96  prop_solver_calls:                      33
% 2.60/0.96  prop_fast_solver_calls:                 652
% 2.60/0.96  smt_solver_calls:                       0
% 2.60/0.96  smt_fast_solver_calls:                  0
% 2.60/0.96  prop_num_of_clauses:                    3517
% 2.60/0.96  prop_preprocess_simplified:             6049
% 2.60/0.96  prop_fo_subsumed:                       5
% 2.60/0.96  prop_solver_time:                       0.
% 2.60/0.96  smt_solver_time:                        0.
% 2.60/0.96  smt_fast_solver_time:                   0.
% 2.60/0.96  prop_fast_solver_time:                  0.
% 2.60/0.96  prop_unsat_core_time:                   0.
% 2.60/0.96  
% 2.60/0.96  ------ QBF
% 2.60/0.96  
% 2.60/0.96  qbf_q_res:                              0
% 2.60/0.96  qbf_num_tautologies:                    0
% 2.60/0.96  qbf_prep_cycles:                        0
% 2.60/0.96  
% 2.60/0.96  ------ BMC1
% 2.60/0.96  
% 2.60/0.96  bmc1_current_bound:                     -1
% 2.60/0.96  bmc1_last_solved_bound:                 -1
% 2.60/0.96  bmc1_unsat_core_size:                   -1
% 2.60/0.96  bmc1_unsat_core_parents_size:           -1
% 2.60/0.96  bmc1_merge_next_fun:                    0
% 2.60/0.96  bmc1_unsat_core_clauses_time:           0.
% 2.60/0.96  
% 2.60/0.96  ------ Instantiation
% 2.60/0.96  
% 2.60/0.96  inst_num_of_clauses:                    855
% 2.60/0.96  inst_num_in_passive:                    376
% 2.60/0.96  inst_num_in_active:                     449
% 2.60/0.96  inst_num_in_unprocessed:                30
% 2.60/0.96  inst_num_of_loops:                      590
% 2.60/0.96  inst_num_of_learning_restarts:          0
% 2.60/0.96  inst_num_moves_active_passive:          134
% 2.60/0.96  inst_lit_activity:                      0
% 2.60/0.96  inst_lit_activity_moves:                0
% 2.60/0.96  inst_num_tautologies:                   0
% 2.60/0.96  inst_num_prop_implied:                  0
% 2.60/0.96  inst_num_existing_simplified:           0
% 2.60/0.96  inst_num_eq_res_simplified:             0
% 2.60/0.96  inst_num_child_elim:                    0
% 2.60/0.96  inst_num_of_dismatching_blockings:      561
% 2.60/0.96  inst_num_of_non_proper_insts:           1044
% 2.60/0.96  inst_num_of_duplicates:                 0
% 2.60/0.96  inst_inst_num_from_inst_to_res:         0
% 2.60/0.96  inst_dismatching_checking_time:         0.
% 2.60/0.96  
% 2.60/0.96  ------ Resolution
% 2.60/0.96  
% 2.60/0.96  res_num_of_clauses:                     0
% 2.60/0.96  res_num_in_passive:                     0
% 2.60/0.96  res_num_in_active:                      0
% 2.60/0.96  res_num_of_loops:                       85
% 2.60/0.96  res_forward_subset_subsumed:            54
% 2.60/0.96  res_backward_subset_subsumed:           6
% 2.60/0.96  res_forward_subsumed:                   0
% 2.60/0.96  res_backward_subsumed:                  0
% 2.60/0.96  res_forward_subsumption_resolution:     0
% 2.60/0.96  res_backward_subsumption_resolution:    0
% 2.60/0.96  res_clause_to_clause_subsumption:       908
% 2.60/0.96  res_orphan_elimination:                 0
% 2.60/0.96  res_tautology_del:                      128
% 2.60/0.96  res_num_eq_res_simplified:              0
% 2.60/0.96  res_num_sel_changes:                    0
% 2.60/0.96  res_moves_from_active_to_pass:          0
% 2.60/0.96  
% 2.60/0.96  ------ Superposition
% 2.60/0.96  
% 2.60/0.96  sup_time_total:                         0.
% 2.60/0.96  sup_time_generating:                    0.
% 2.60/0.96  sup_time_sim_full:                      0.
% 2.60/0.96  sup_time_sim_immed:                     0.
% 2.60/0.96  
% 2.60/0.96  sup_num_of_clauses:                     232
% 2.60/0.96  sup_num_in_active:                      114
% 2.60/0.96  sup_num_in_passive:                     118
% 2.60/0.96  sup_num_of_loops:                       116
% 2.60/0.96  sup_fw_superposition:                   103
% 2.60/0.96  sup_bw_superposition:                   146
% 2.60/0.96  sup_immediate_simplified:               7
% 2.60/0.96  sup_given_eliminated:                   0
% 2.60/0.96  comparisons_done:                       0
% 2.60/0.96  comparisons_avoided:                    0
% 2.60/0.96  
% 2.60/0.96  ------ Simplifications
% 2.60/0.96  
% 2.60/0.96  
% 2.60/0.96  sim_fw_subset_subsumed:                 5
% 2.60/0.96  sim_bw_subset_subsumed:                 0
% 2.60/0.96  sim_fw_subsumed:                        1
% 2.60/0.96  sim_bw_subsumed:                        0
% 2.60/0.96  sim_fw_subsumption_res:                 2
% 2.60/0.96  sim_bw_subsumption_res:                 0
% 2.60/0.96  sim_tautology_del:                      8
% 2.60/0.96  sim_eq_tautology_del:                   0
% 2.60/0.96  sim_eq_res_simp:                        0
% 2.60/0.96  sim_fw_demodulated:                     0
% 2.60/0.96  sim_bw_demodulated:                     2
% 2.60/0.96  sim_light_normalised:                   0
% 2.60/0.96  sim_joinable_taut:                      0
% 2.60/0.96  sim_joinable_simp:                      0
% 2.60/0.96  sim_ac_normalised:                      0
% 2.60/0.96  sim_smt_subsumption:                    0
% 2.60/0.96  
%------------------------------------------------------------------------------
